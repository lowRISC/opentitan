#include <string.h>

#include "sw/lib/common.h"
#include "sw/lib/irq.h"

extern int main(void);

void _crt(void) __attribute__((section(".crt")));
void _crt(void) {
  extern char _sdata[];
  extern char _idata[];
  extern char _edata[];
  extern char _bss_start[];
  extern char _bss_end[];

  update_mtvec();
  memcpy(_sdata, _idata, _edata - _sdata);
  memset(_bss_start, 0, _bss_end - _bss_start);

  main();
}
