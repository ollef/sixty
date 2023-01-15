#include "reference_counting.h"
#include <mimalloc.h>

#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#define debug_printf(...) // printf(__VA_ARGS__)

const uintptr_t INLINE_SIZE_MASK = 0xFF << 3;

// heap pointer: | 45 bits pointer data | 8 bits constructor tag | 8 bits word size | 2 bits object type | 1 |

static
void print_heap_object(uintptr_t heap_object) {
  char* pointer = sixten_heap_object_pointer(heap_object);
  debug_printf("pointer: 0x%" PRIxPTR, (uintptr_t)pointer);
  uintptr_t constructor_tag = heap_object_constructor_tag(heap_object);
  debug_printf(", constructor_tag: %" PRIuPTR, constructor_tag);
  uintptr_t inline_size = heap_object & INLINE_SIZE_MASK;
  debug_printf(", inline_size: %" PRIuPTR, inline_size);
  uintptr_t object_type = heap_object & ~(~0ul << 3);
  debug_printf(", object_type: %" PRIuPTR, object_type);
}

int sixten_is_heap_object(uintptr_t word) {
  return word & 0x1;
}

uintptr_t sixten_heap_object_size(uintptr_t word) {
  uintptr_t inline_size = word & INLINE_SIZE_MASK;
  if (unlikely(inline_size == INLINE_SIZE_MASK)) {
    return *(uintptr_t*)(sixten_heap_object_pointer(word) - sizeof(char*));
  }
  return inline_size;
}

char* sixten_heap_object_pointer(uintptr_t word) {
  return (char*)((uintptr_t)((intptr_t)word >> 19) << 3);
}

// If we know that the constructor tag is <= 5 bits, we can get the pointer
// with one instead of two shifts.
char* sixten_heap_object_pointer_5bit_tag(uintptr_t word) {
  return (char*)((intptr_t)word >> 16);
}

uintptr_t sixten_heap_object_constructor_tag(uintptr_t word) {
  return (word >> 11) & 0xFF;
}

uintptr_t sixten_allocate(uintptr_t constructor_tag, uintptr_t size){
  debug_printf("heap allocating %" PRIuPTR " bytes \n", size);
  uintptr_t inline_size = size;
  uintptr_t object_size = size;
  uintptr_t object_pointer_offset = 0;
  char* object_pointer = heap_pointer;

  // If size is too large to be stored in free bits in the pointer, make room
  // for it to be stored just before the heap object's data.
  if (unlikely(size >= INLINE_SIZE_MASK)) {
    inline_size = INLINE_SIZE_MASK;
    object_size = size + sizeof(char*);
    object_pointer_offset = sizeof(char*);
  }

  // Make space for reference count.
  uintptr_t alloc_size = object_size + sizeof(char*);

  char* heap_pointer = mi_malloc(alloc_size);
  char* object_pointer = heap_pointer + object_pointer_offset;

  // Store initial reference count.
  *(uintptr_t*)object_pointer = 1;

  // Actually store the size before the heap object if the size was too large
  // to be inline.
  if (unlikely(size >= INLINE_SIZE_MASK)) {
    *(uintptr_t*)heap_pointer = size;
  }

  uintptr_t result
    = ((uintptr_t)object_pointer << 16)
    | ((uintptr_t)constructor_tag << 11)
    | (uintptr_t)inline_size
    | 1;

  debug_printf("heap allocated object ");
  print_heap_object(result);
  debug_printf("\n");

  return result;
}

void sixten_retain(uintptr_t word) {
  if (!sixten_is_heap_object(word))
    return;
  char* pointer = sixten_heap_object_pointer(word);
  *(uintptr_t*)pointer += 1;
}

void sixten_retains(char* pointer, uintptr_t size) {
  for (char* p = pointer, end = pointer + size; p < end; p += sizeof(char*)) {
    sixten_retain(*(uintptr_t*)p);
  }
}

void sixten_release(uintptr_t word) {
  if (!sixten_is_heap_object(word))
    return;
  char* pointer = sixten_heap_object_pointer(word);
  *(uintptr_t)pointer -= 1;
  uintptr_t rc = *(uintptr_t*)pointer;
  if (rc > 0)
    return;
  uintptr_t size = sixten_heap_object_size(word);
  sixten_releases(pointer + sizeof(char*), size);
  if (unlikely(size >= INLINE_SIZE_MASK))
    pointer -= sizeof(char*);
  mi_free(pointer);
}

void sixten_releases(char* pointer, uintptr_t size) {
  for (char* p = pointer, end = p + size; p < end; p += sizeof(char*)) {
    sixten_release(*(uintptr_t*)p);
  }
};
