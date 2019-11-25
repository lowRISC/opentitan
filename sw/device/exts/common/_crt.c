// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/irq.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mem.h"
#include "sw/device/lib/base/types.h"

extern int main(void);

LINK_SECTION(".crt")
void _crt(void) {
  extern char _svectors[];
  extern char _sdata[];
  extern char _idata[];
  extern char _edata[];
  extern char _bss_start[];
  extern char _bss_end[];

  update_mtvec(_svectors);
  base_memcpy(_sdata, _idata, _edata - _sdata);
  base_memset(_bss_start, 0, _bss_end - _bss_start);

  main();
}
