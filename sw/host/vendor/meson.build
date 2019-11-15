# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

libmpsse = declare_dependency(
  link_with: static_library(
    'mpsse',
    sources: [
      '../vendor/mpsse/mpsse.c',
      '../vendor/mpsse/support.c'
    ],
    c_args: [
      '-I' + meson.source_root() + '/sw/host/vendor/mpsse'
    ],
    dependencies: [
      dependency('libftdi1', native: true),
      dependency('libusb-1.0', native: true),
    ],
    native: true,
  ),
)
