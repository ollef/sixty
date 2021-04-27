#pragma once

#include <stdint.h>

struct init_result {
  char* heap_pointer;
  char* heap_limit;
};

struct init_result init_garbage_collector();

struct heap_alloc_result {
  intptr_t result;
  char* heap_pointer;
  char* heap_limit;
};

struct shadow_stack_frame_entry {
  uintptr_t size;
  char* data;
};

struct shadow_stack_frame {
  struct shadow_stack_frame* previous;
  uintptr_t entry_count;
  struct shadow_stack_frame_entry entries[];
};

struct heap_alloc_result heap_alloc(struct shadow_stack_frame* shadow_stack, char* heap_pointer, char* heap_limit, char constructor_tag, uintptr_t size);
int is_heap_pointer(intptr_t word);
uintptr_t heap_object_size(intptr_t word);
char* heap_object_pointer(intptr_t word);
char* heap_object_pointer_5bit_tag(intptr_t word);
