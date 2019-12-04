// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/common.h"
#include "sw/device/lib/irq.h"

extern int main(void);

void _crt(void) __attribute__((section(".crt")));
void _crt(void) {
  extern char _svectors[];
  extern char _sdata[];
  extern char _idata[];
  extern char _edata[];
  extern char _bss_start[];
  extern char _bss_end[];

  update_mtvec(_svectors);
  memcpy(_sdata, _idata, _edata - _sdata);
  memset(_bss_start, 0, _bss_end - _bss_start);

  main();

  while(1) {
    asm volatile("wfi");
  }
}
