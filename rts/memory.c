#include "memory.h"

#include <stdlib.h>

static const uintptr_t TAG_BITS = 16;
static const uintptr_t TAG_MASK = ((uintptr_t)1 << TAG_BITS) - 1;

struct header {
  uint32_t pointers;
};

uintptr_t sixten_heap_allocate(uint64_t tag, uint32_t pointers, uint32_t non_pointer_bytes) {
  uintptr_t bytes = (uintptr_t)pointers * sizeof(void*) + (uintptr_t)non_pointer_bytes;
  uint8_t* pointer = 0;

  if (bytes > 0) {
    pointer = calloc(sizeof(struct header) + bytes, 1);
  }

  struct header* header = (struct header*)pointer;
  header->pointers = pointers;

  pointer += sizeof(struct header);

  return (uintptr_t)pointer << TAG_BITS | (uintptr_t)(tag & TAG_MASK);
}

struct sixten_reference sixten_heap_payload(uintptr_t heap_object) {
  uint8_t* pointer = (uint8_t*)((intptr_t)heap_object >> TAG_BITS);
  if (pointer == 0) {
    return (struct sixten_reference) {
      .pointers = 0,
      .non_pointers = 0,
    };
  }

  struct header* header = (struct header*)(pointer - sizeof(struct header));

  return (struct sixten_reference) {
    .pointers = pointer,
    .non_pointers = pointer + header->pointers * sizeof(void*),
  };
}

uint64_t sixten_heap_tag(uintptr_t heap_object) {
  return (uint64_t)(heap_object & TAG_MASK);
}
