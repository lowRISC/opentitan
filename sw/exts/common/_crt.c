// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#include "common.h"
#include "irq.h"

extern int main(int, char **);

void _crt(void) NO_RETURN __attribute__((section(".crt")));
void _crt(void) {
  extern char _sdata[];
  extern char _idata[];
  extern char _edata[];
  extern char _bss_start[];
  extern char _bss_end[];

  update_mtvec();
  memcpy(_sdata, _idata, _edata - _sdata);
  memset(_bss_start, 0, _bss_end - _bss_start);

  main(0, NULL);
  while (true) {
    __asm__ volatile("wfi");
  }
}
