#pragma once

#include <stdint.h>

struct sixten_reference {
  uint8_t* pointers;
  uint8_t* non_pointers;
};

uintptr_t sixten_heap_allocate(uint64_t tag, uint32_t pointers, uint32_t non_pointer_bytes);
struct sixten_reference sixten_heap_payload(uintptr_t heap_object);
uint64_t sixten_heap_tag(uintptr_t heap_object);
