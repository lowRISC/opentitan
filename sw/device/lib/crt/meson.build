# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Assembly utility functions for initializing C runtime (sw_lib_crt).
sw_lib_crt = declare_dependency(
  link_with: static_library(
    'crt_ot',
    sources: ['crt.S'],
  )
)
