#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

uint8_t peek(uint8_t* ptr, size_t index) {
  return ptr[index];
}

void poke(uint8_t* ptr, size_t index, uint8_t byte) {
  ptr[index] = byte;
}

bool ptr_eq(void *ptr_a, void *ptr_b) {
  return ptr_a == ptr_b;
}
