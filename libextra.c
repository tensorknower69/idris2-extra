#include <stddef.h>
#include <stdio.h>

unsigned char peek(void* ptr, size_t index) {
  return ((unsigned char*) ptr)[index];
}

void poke(void* ptr, size_t index, unsigned char byte) {
  ((unsigned char*) ptr)[index] = byte;
}
