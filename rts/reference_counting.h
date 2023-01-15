#pragma once

#include <stdint.h>

int sixten_is_heap_object(uintptr_t word);
uintptr_t sixten_heap_object_size(uintptr_t word);
char* sixten_heap_object_pointer(uintptr_t word);
char* sixten_heap_object_pointer_5bit_tag(uintptr_t word);
uintptr_t sixten_heap_object_constructor_tag(uintptr_t word);

uintptr_t sixten_allocate(uintptr_t constructor_tag, uintptr_t size);
void sixten_retain(uintptr_t word);
void sixten_retains(char* pointer, uintptr_t size);
void sixten_release(uintptr_t word);
void sixten_releases(char* pointer, uintptr_t size);
