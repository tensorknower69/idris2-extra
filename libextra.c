#include <stddef.h>
#include <stdio.h>
#include <stdint.h>

uint8_t peek(uint8_t* ptr, size_t index) {
  return ptr[index];
}

void poke(uint8_t* ptr, size_t index, uint8_t byte) {
  ptr[index] = byte;
}
