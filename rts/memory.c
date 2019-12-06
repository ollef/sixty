#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
  size_t data;
} vix_heap_word_t;

typedef struct {
  int32_t reference_count : 29;
  enum {
    managed = 0,
    unmanaged = 1,
    finalized = 2,
  } type : 2;
  enum {
    single = 0,
    multi = 1,
  } threading : 1;
  uint32_t size;
} vix_object_header_t;

typedef struct {
  void (*finalize)(void*);
  vix_object_header_t header;
} vix_finalized_object_header_t;

/*----------------------------------------------------------------------------*/

int vix_heap_word_is_pointer(vix_heap_word_t word) {
  return word.data & 1;
}

vix_heap_word_t* vix_heap_word_pointer(vix_heap_word_t word) {
  return (vix_heap_word_t*) (word.data & ~1);
}

void vix_assign_pointer(vix_heap_word_t* assignee, vix_heap_word_t* value) {
  assignee->data = (size_t) value | 1;
}

vix_heap_word_t* vix_data_from_header(vix_object_header_t* header) {
  return (vix_heap_word_t*) ((uint8_t*) header + sizeof(vix_object_header_t));
}

vix_object_header_t* vix_header_from_data(vix_heap_word_t* data) {
  return (vix_object_header_t*) ((uint8_t*) data - sizeof(vix_object_header_t));
}

vix_finalized_object_header_t* vix_finalized_from_header(vix_object_header_t* header) {
  return (vix_finalized_object_header_t*) ((uint8_t*) header - sizeof(vix_finalized_object_header_t) + sizeof(vix_object_header_t));
}

/*----------------------------------------------------------------------------*/

vix_heap_word_t* vix_allocate_managed(uint32_t num_bytes) {
  vix_object_header_t* result = calloc(sizeof(vix_object_header_t) + num_bytes, 1);
  *result = (vix_object_header_t) {
    .reference_count = 1,
    .type = managed,
    .threading = single,
    .size = num_bytes,
  };
  return vix_data_from_header(result);
}

vix_heap_word_t* vix_allocate_unmanaged(uint32_t num_bytes) {
  vix_object_header_t* result = calloc(sizeof(vix_object_header_t) + num_bytes, 1);
  *result = (vix_object_header_t) {
    .reference_count = 1,
    .type = unmanaged,
    .threading = single,
    .size = num_bytes,
  };
  return (void*) vix_data_from_header(result);
}

vix_heap_word_t* vix_allocate_finalized(void (*finalize)(void*), uint32_t num_bytes) {
  vix_finalized_object_header_t* result = calloc(sizeof(vix_finalized_object_header_t) + num_bytes, 1);
  *result = (vix_finalized_object_header_t) {
    .finalize = finalize,
    .header = (vix_object_header_t) {
      .reference_count = 1,
      .type = finalized,
      .threading = single,
      .size = num_bytes,
    },
  };
  return vix_data_from_header(&result->header);
}

void vix_increase_reference_count(vix_heap_word_t* data) {
  vix_object_header_t* header = vix_header_from_data(data);
  switch (header->threading) {
    case single:;
      ++header->reference_count;
      break;
    case multi:;
      atomic_fetch_add_explicit((atomic_int*) header, 1, memory_order_relaxed);
      break;
  }
}

void vix_deallocate(vix_object_header_t* header);

void vix_decrease_reference_count(vix_heap_word_t* data) {
  printf("decrease ref count %p\n", data);
  vix_object_header_t* header = vix_header_from_data(data);
  int32_t old_ref_count;
  switch (header->threading) {
    case single:;
      old_ref_count = header->reference_count--;
      break;
    case multi:;
      old_ref_count = atomic_fetch_sub_explicit((atomic_int*) header, 1, memory_order_relaxed);
      break;
  }
  if (old_ref_count == 1) {
    printf("ref count 0\n");
    vix_deallocate(header);
  }
}

void vix_deallocate(vix_object_header_t* header) {
  switch (header->type) {
    case managed:;
      printf("dealloc managed\n");
      uint32_t word_size = header->size / sizeof(vix_heap_word_t);
      printf("size %d\n", word_size);
      vix_heap_word_t* data = vix_data_from_header(header);
      for (uint32_t i = 0; i < word_size; ++i) {
        vix_heap_word_t word = data[i];
        if (vix_heap_word_is_pointer(word)) {
          vix_decrease_reference_count(vix_heap_word_pointer(word));
        }
      }
      free(header);
      break;

    case unmanaged:;
      printf("dealloc pod\n");
      free(header);
      break;

    case finalized:;
      printf("dealloc finalized\n");
      vix_finalized_object_header_t* finalized = vix_finalized_from_header(header);
      finalized->finalize(vix_data_from_header(header));
      free(finalized);
      break;

    default:;
      break;
  }
}

/*----------------------------------------------------------------------------*/

void vix_share_with_thread(vix_heap_word_t* data) {
  vix_object_header_t* header = vix_header_from_data(data);
  switch (header->type) {
    case managed:;
    case finalized:;
      switch (header->threading) {
        case single:;
          header->threading = multi;
          uint32_t word_size = header->size / sizeof(vix_heap_word_t);
          vix_heap_word_t* data = vix_data_from_header(header);
          for (uint32_t i = 0; i < word_size; ++i) {
            vix_heap_word_t word = data[i];
            if (vix_heap_word_is_pointer(word)) {
              vix_share_with_thread(vix_heap_word_pointer(word));
            }
          }
        case multi:;
          break;
      }
      break;

    case unmanaged:;
      break;

    default:;
      break;
  }
}

/*----------------------------------------------------------------------------*/

void my_finalizer(void* data) {
  printf("finalizing %p\n", data);
}

int main() {
  printf("%d\n", sizeof(vix_object_header_t));
  printf("%d\n", sizeof(vix_heap_word_t));
  vix_heap_word_t* obj1 = vix_allocate_managed(3 * sizeof(vix_heap_word_t));
  vix_heap_word_t* obj2 = vix_allocate_managed(2 * sizeof(vix_heap_word_t));
  vix_heap_word_t* obj3 = vix_allocate_finalized(my_finalizer, 2 * sizeof(vix_heap_word_t));
  printf("obj1 %p\n", obj1);
  printf("obj2 %p\n", obj2);
  printf("obj3 %p\n", obj3);
  vix_assign_pointer(&obj1[1], obj2);
  vix_assign_pointer(&obj2[1], obj3);
  vix_decrease_reference_count(obj1);
}
