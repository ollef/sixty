#include "memory.h"

#include <stdlib.h>
#include <string.h>

static const uintptr_t TAG_BITS = 16;
static const uintptr_t TAG_MASK = ((uintptr_t)1 << TAG_BITS) - 1;

struct header {
  uint32_t reference_count;
  uint32_t pointers;
};

uintptr_t sixten_heap_allocate(uint64_t tag, uint32_t pointers, uint32_t non_pointer_bytes) {
  uintptr_t bytes = (uintptr_t)pointers * sizeof(void*) + (uintptr_t)non_pointer_bytes;
  uint8_t* pointer = 0;

  if (bytes > 0) {
    pointer = calloc(sizeof(struct header) + bytes, 1);
    struct header* header = (struct header*)pointer;
    *header = (struct header) {
      .pointers = pointers,
      .reference_count = 1,
    };
    pointer += sizeof(struct header);
  }

  return (uintptr_t)pointer << TAG_BITS | (uintptr_t)(tag & TAG_MASK);
}

static uint8_t* heap_object_pointer(uintptr_t heap_object) {
  return (uint8_t*)((intptr_t)heap_object >> TAG_BITS);
}

struct sixten_reference sixten_heap_payload(uintptr_t heap_object) {
  uint8_t* pointer = heap_object_pointer(heap_object);

  if (pointer == 0) {
    return (struct sixten_reference) {
      .pointers = 0,
      .non_pointers = 0,
    };
  }

  struct header* header = (struct header*)(pointer - sizeof(struct header));

  return (struct sixten_reference) {
    .pointers = (uintptr_t*)pointer,
    .non_pointers = pointer + header->pointers * sizeof(void*),
  };
}

uint64_t sixten_heap_tag(uintptr_t heap_object) {
  return (uint64_t)(heap_object & TAG_MASK);
}

void sixten_copy(
  struct sixten_reference dst,
  struct sixten_reference src,
  uint32_t pointers,
  uint32_t non_pointer_bytes
) {
  memcpy(dst.pointers, src.pointers, sizeof(void*) * pointers);
  memcpy(dst.non_pointers, src.non_pointers, non_pointer_bytes);
}

void sixten_increase_reference_count(uintptr_t heap_object) {
  uint8_t* pointer = heap_object_pointer(heap_object);
  if (pointer == 0) {
    return;
  }

  struct header* header = (struct header*)(pointer - sizeof(struct header));
  ++header->reference_count;
}

void sixten_increase_reference_counts(uintptr_t* data, uint32_t count) {
  for (uint32_t i = 0; i < count; ++i) {
    sixten_increase_reference_count(data[i]);
  }
}

void sixten_decrease_reference_count(uintptr_t heap_object) {
  uint8_t* pointer = heap_object_pointer(heap_object);
  if (pointer == 0) {
    return;
  }

  struct header* header = (struct header*)(pointer - sizeof(struct header));
  --header->reference_count;
  if (header->reference_count == 0) {
    sixten_decrease_reference_counts((uintptr_t*)pointer, header->pointers);
    free(header);
  }
}

void sixten_decrease_reference_counts(uintptr_t* data, uint32_t count) {
  for (uint32_t i = 0; i < count; ++i) {
    sixten_decrease_reference_count(data[i]);
  }
}
