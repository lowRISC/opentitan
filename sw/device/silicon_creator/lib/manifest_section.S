// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest_size.h"

  /**
   * Manifest for boot stages stored in flash.
   */
  .section .manifest, "a"
  .balign 4
  .global kManifest
  .type kManifest, @object
kManifest:
  .zero MANIFEST_SIZE
  .size kManifest, .-kManifest
