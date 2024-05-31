#pragma once

#include <stdint.h>

struct sixten_reference {
  uintptr_t* pointers;
  uint8_t* non_pointers;
};

uintptr_t sixten_heap_allocate(uint64_t tag, uint32_t pointers, uint32_t non_pointer_bytes);
struct sixten_reference sixten_heap_payload(uintptr_t heap_object);
uint64_t sixten_heap_tag(uintptr_t heap_object);
void sixten_copy(
  struct sixten_reference dst,
  struct sixten_reference src,
  uint32_t pointers,
  uint32_t non_pointer_bytes
);
void sixten_increase_reference_count(uintptr_t heap_object);
void sixten_decrease_reference_count(uintptr_t heap_object);
void sixten_decrease_reference_counts(uintptr_t* data, uint32_t count);
