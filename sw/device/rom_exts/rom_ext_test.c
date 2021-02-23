// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>

#include "sw/device/lib/runtime/hart.h"

int main(int argc, char *argv[]);

#include "sw/device/rom_exts/rom_ext.h"

void rom_ext_boot(void) {
  (void)main(0, NULL);

  while (true) {
    wait_for_interrupt();
  }
}
