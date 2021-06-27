#define _DEFAULT_SOURCE
#include "garbage_collector.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

const uintptr_t INLINE_SIZE_CUTOFF = 0xFF << 3;

// heap pointer: | 45 bits pointer data | 8 bits constructor tag | 8 bits word size | 2 bits object type | 1 |

struct collector_info {
  char* heap_start_pointer;
  uintptr_t last_occupied_size;
};

static
uintptr_t round_up_to_multiple_of(uintptr_t multiple, uintptr_t x) {
  uintptr_t remainder = x % multiple;
  return remainder == 0 ? x : x - remainder + multiple;
}

uintptr_t page_size() {
  static uintptr_t result = 0;
  if (!result) {
    result = sysconf(_SC_PAGESIZE);
  }
  return result;
}

struct init_result init_garbage_collector() {
  uintptr_t size = round_up_to_multiple_of(page_size(), 4096);
  char* heap_start_pointer = mmap(0, size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  if (heap_start_pointer == MAP_FAILED) {
    exit(EXIT_FAILURE);
  }
  // Put collector info right after the heap limit.
  char* heap_limit_with_collector_info = heap_start_pointer + size;
  char* heap_limit = heap_limit_with_collector_info - sizeof(struct collector_info);
  struct collector_info* collector_info = (struct collector_info*) heap_limit;
  *collector_info = (struct collector_info) {
    .heap_start_pointer = heap_start_pointer,
    .last_occupied_size = (heap_limit - heap_start_pointer) / 2,
  };
  return (struct init_result) {
    .heap_pointer = heap_start_pointer,
    .heap_limit = heap_limit,
  };
}

static
uintptr_t get_forwarded_object_or_0(uintptr_t object, char* new_heap_start, char* new_heap_end) {
  char* object_data = heap_object_pointer(object);
  uintptr_t first_word = *(uintptr_t*)object_data;
  if (is_heap_pointer(first_word)) {
    char* pointer = heap_object_pointer(first_word);
    if (new_heap_start <= pointer && pointer < new_heap_end) {
      return (object & (~0ul >> 45)) | ((intptr_t)pointer << 19);
    }
  }
  return 0;
}

struct collection_result {
  char* heap_pointer;
  char* heap_limit;
};

static
uintptr_t copy(uintptr_t heap_object, char** new_heap_pointer_pointer, char* new_heap_start, char* new_heap_end) {
  uintptr_t size = heap_object_size(heap_object);
  // If the size is 0 we don't have space to leave a forwarding pointer, but we
  // also have nothing to copy. :)
  if (size == 0) {
    return heap_object;
  }
  // If we have a forwarding pointer, we're already done.
  uintptr_t forwarded_object = get_forwarded_object_or_0(heap_object, new_heap_start, new_heap_end);
  if (forwarded_object) {
    return forwarded_object;
  }
  // If the size is larger than the inline size cutoff we store the size just
  // before the copied new heap object.
  if (unlikely(size >= INLINE_SIZE_CUTOFF)) {
    *(uintptr_t*)(*new_heap_pointer_pointer) = size;
    *new_heap_pointer_pointer += sizeof(char*);
  }
  char* copied_object_start = *new_heap_pointer_pointer;
  *new_heap_pointer_pointer = copied_object_start + size;
  char* object_data_pointer = heap_object_pointer(heap_object);
  // Copy old to new heap data.
  memcpy(copied_object_start, object_data_pointer, size);
  // Construct new heap object from new pointer + old metadata.
  uintptr_t new_heap_object = (heap_object & ~(~0ul << 19)) | ((uintptr_t)copied_object_start << 19);
  // Install forwarding pointer in old heap object data.
  *(uintptr_t*)object_data_pointer = new_heap_object;
  return new_heap_object;
}

static
struct collection_result collect(struct shadow_stack_frame* shadow_stack, char* heap_pointer, char* heap_limit, uintptr_t minimum_free_space) {
  struct collector_info* collector_info = (struct collector_info*) heap_limit;
  char* heap_start_pointer = collector_info->heap_start_pointer;
  uintptr_t old_size = heap_pointer - heap_start_pointer;
  // We're aiming at allocating 2x the occupied space, but we don't know yet
  // how much space will actually be occupied after the collection, so we take
  // a guess based on the occupied size of the last collection, ensuring we
  // have at least minimum_free_space.
  uintptr_t estimated_new_size = collector_info->last_occupied_size * 2;
  uintptr_t minimum_new_size = old_size + minimum_free_space;
  uintptr_t new_size =
    round_up_to_multiple_of(
      page_size(),
      (estimated_new_size > minimum_new_size ? estimated_new_size : minimum_new_size) +
        sizeof(struct collector_info));

  char* new_heap_start_pointer = mmap(0, new_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  if (new_heap_start_pointer == MAP_FAILED) {
    exit(EXIT_FAILURE);
  }
  char* new_heap_pointer = new_heap_start_pointer;
  char* new_heap_end_pointer = new_heap_start_pointer + new_size;
  // Copy stack roots.
  while (shadow_stack) {
    uintptr_t entry_count = shadow_stack->entry_count;
    for (uintptr_t entry_index = 0; entry_index < entry_count; ++entry_index) {
      struct shadow_stack_frame_entry* entry = &shadow_stack->entries[entry_index];
      uintptr_t* entry_end = (uintptr_t*)(entry->data + entry->size);
      for (uintptr_t* entry_word_pointer = (uintptr_t*)entry->data; entry_word_pointer < entry_end; ++entry_word_pointer) {
        uintptr_t entry_word = *entry_word_pointer;
        if (is_heap_pointer(entry_word)) {
          *entry_word_pointer = copy(entry_word, &new_heap_pointer, new_heap_start_pointer, new_heap_end_pointer);
        }
      }
    }
    shadow_stack = shadow_stack->previous;
  }
  // Scan copied heap objects.
  char* scan_pointer = new_heap_start_pointer;
  while (scan_pointer < new_heap_pointer) {
    uintptr_t scan_word = *(uintptr_t*)scan_pointer;
    if (is_heap_pointer(scan_word)) {
      *(uintptr_t*)scan_pointer = copy(scan_word, &new_heap_pointer, new_heap_start_pointer, new_heap_end_pointer);
    }
    scan_pointer += sizeof(char*);
  }
  uintptr_t occupied_size = new_heap_pointer - new_heap_start_pointer;
  // Now we know the exact occupied size, so we see if we should allocate some
  // more space to reach 2x that.
  uintptr_t minimum_desired_size = round_up_to_multiple_of(page_size(), occupied_size * 2 + sizeof(struct collector_info));
  if (minimum_desired_size > new_size) {
    char* result = mmap(new_heap_end_pointer, minimum_desired_size - new_size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    if (result != MAP_FAILED) {
      new_heap_end_pointer = result;
    }
  }
  // Store the collector info just past the new heap limit.
  char* new_heap_limit = new_heap_end_pointer - sizeof(struct collector_info);
  *(struct collector_info*)new_heap_limit = (struct collector_info) {
    .heap_start_pointer = new_heap_start_pointer,
    .last_occupied_size = occupied_size,
  };
  return (struct collection_result) {
    .heap_pointer = new_heap_pointer,
    .heap_limit = new_heap_limit,
  };
}

struct heap_alloc_result __attribute((regcall)) heap_alloc(struct shadow_stack_frame* shadow_stack, char* heap_pointer, char* heap_limit, char constructor_tag, uintptr_t size) {
  uintptr_t inline_size = size;
  uintptr_t object_size = size;
  char* object_pointer = heap_pointer;
  // If size is too large to be stored in free bits in the pointer, make room
  // for it to be stored just before the heap object's data.
  if (unlikely(size >= INLINE_SIZE_CUTOFF)) {
    inline_size = INLINE_SIZE_CUTOFF;
    object_size = size + sizeof(char*);
    object_pointer = heap_pointer + sizeof(char*);
  }
  char* new_heap_pointer = heap_pointer + object_size;
  // We've out of space, so trigger a collection.
  if (unlikely(new_heap_pointer > heap_limit)) {
    struct collection_result collection_result = collect(shadow_stack, heap_pointer, heap_limit, object_size);
    heap_pointer = collection_result.heap_pointer;
    heap_limit = collection_result.heap_limit;
    object_pointer = heap_pointer;
    if (unlikely(size >= INLINE_SIZE_CUTOFF)) {
      object_pointer = heap_pointer + sizeof(char*);
    }
    new_heap_pointer = heap_pointer + object_size;
  }
  // Actually store the size before the heap object if the size was too large
  // to be inline.
  if (unlikely(inline_size == INLINE_SIZE_CUTOFF)) {
    *(uintptr_t*)heap_pointer = size;
  }
  uintptr_t result
    = ((uintptr_t)object_pointer << 16)
    | ((uintptr_t)constructor_tag << 11)
    | (uintptr_t)inline_size
    | 1;
  return (struct heap_alloc_result) {
    .result = result,
    .heap_pointer = new_heap_pointer,
    .heap_limit = heap_limit,
  };
}

int is_heap_pointer(uintptr_t word) {
  return word & 0x1;
}

uintptr_t heap_object_size(uintptr_t word) {
  uintptr_t inline_size = word & (0xFF << 3);
  if (unlikely(inline_size == (0xFF << 3))) {
    return *(uintptr_t*)(heap_object_pointer(word) - sizeof(char*));
  }
  return inline_size;
}

uintptr_t heap_object_constructor_tag(uintptr_t word) {
  return (word >> 11) & 0xFF;
}

char* heap_object_pointer(uintptr_t word) {
  return (char*)((uintptr_t)((intptr_t)word >> 19) << 3);
}

// If we know that the constructor tag is <= 5 bits, we can get the pointer
// with one instead of two shifts.
char* heap_object_pointer_5bit_tag(uintptr_t word) {
  return (char*)(word >> 16);
}
