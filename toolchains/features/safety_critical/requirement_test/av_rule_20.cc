#include <setjmp.h>
#include <cstdint>

jmp_buf buf;

void FailsAvRule20(void) {
  uint64_t r = setjmp(buf);
  longjmp(buf, 42);
}