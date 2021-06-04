// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Manifest for boot stages stored in flash.
 */

  #include "sw/device/silicon_creator/lib/manifest_size.h"

  .section .manifest, "a"
  .globl kManifest

kManifest:
  .rept MANIFEST_SIZE
  .byte 0x0
  .endr
