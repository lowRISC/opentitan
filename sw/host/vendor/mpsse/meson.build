# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

libmpsse = declare_dependency(
  include_directories : include_directories('.'),
  link_with: static_library(
    'mpsse',
    sources: [
      'mpsse.c',
      'support.c'
    ],
    dependencies: [
      dependency('libftdi1', native: true),
      dependency('libusb-1.0', native: true),
    ],
    native: true,
  ),
)
