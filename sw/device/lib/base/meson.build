# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The OpenTitan "libbase", an extra-trimmed-down libc-like library.
sw_libbase = declare_dependency(
  link_with: static_library(
    'sw_ot_base',
    sources: [
      'abort.c',
      'mem.c',
    ],
  )
)