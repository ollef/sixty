#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

#include "garbage_collector.h"

#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

struct init_result init_garbage_collector() {
  size_t size = 16 * 1024 * 1024;
  char* address = mmap(0, size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  if (address == MAP_FAILED) {
    exit(EXIT_FAILURE);
  }
  return (struct init_result) {
    .heap_pointer = address,
    .heap_limit = address + size,
  };
}

// heap pointer: | 45 bits pointer data | 8 bits constructor tag | 8 bits word size | 2 bits object type | 1 |

struct heap_alloc_result heap_alloc(struct shadow_stack_frame* shadow_stack, char* heap_pointer, char* heap_limit, char constructor_tag, uintptr_t size) {
  uintptr_t inline_size = size;
  uintptr_t object_size = size;
  char* object_pointer = heap_pointer;
  uintptr_t inline_size_cutoff = 0xFF << 3;
  if (unlikely(size >= inline_size_cutoff)) {
    inline_size = inline_size_cutoff;
    object_size = size + sizeof(char*);
    object_pointer = heap_pointer + sizeof(char*);
  }
  char* new_heap_pointer = heap_pointer + object_size;
  if (unlikely(new_heap_pointer > heap_limit)) {
    // TODO: Do GC :)
    exit(0x43A4);
  }
  intptr_t result
    = ((intptr_t)object_pointer << 16)
    | ((intptr_t)constructor_tag << 11)
    | (intptr_t)inline_size
    | 1;
  return (struct heap_alloc_result) {
    .result = result,
    .heap_pointer = new_heap_pointer,
    .heap_limit = heap_limit,
  };
}

int is_heap_pointer(intptr_t word) {
  return word & 0x1;
}

uintptr_t heap_object_size(intptr_t word) {
  uintptr_t inline_size = (uintptr_t)word & (0xFF << 3);
  if (unlikely(inline_size == (0xFF << 3))) {
    return *(uintptr_t*)(heap_object_pointer(word) - sizeof(char*));
  }
  return inline_size;
}

intptr_t heap_object_constructor_tag(intptr_t word) {
  return (word & (0xFF << 11)) >> 11;
}

char* heap_object_pointer(intptr_t word) {
  return (char*)((word >> 19) << 3);
}

// If we know that the constructor tag is <= 5 bits, we can get the pointer
// with one instead of two shifts.
char* heap_object_pointer_5bit_tag(intptr_t word) {
  return (char*)(word >> 16);
}
