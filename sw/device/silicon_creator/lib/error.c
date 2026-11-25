// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/error.h"

rom_error_t rom_error_from_shifted_(uint32_t shifted_err) {
  HARDENED_CHECK_NE(shifted_err, 0);
#if defined(OT_PLATFORM_RV32) && !defined(OT_DISABLE_HARDENING)
  asm volatile("addi %[err], %[err], %[kOk];"
               : [err] "+r"(shifted_err)
               : [kOk] "i"(kErrorOk));
  return (rom_error_t)shifted_err;
#else
  return (rom_error_t)(shifted_err + kErrorOk);
#endif
}
