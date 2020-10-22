# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

libmpsse = declare_dependency(
  link_with: static_library(
    'mpsse',
    sources: [
      'mpsse/mpsse.c',
      'mpsse/support.c'
    ],
    # libmpsse is vendored in, and as such does not conform to our include
    # requirements. This -I argument allows libmpsse to use its existing
    # includes.
    c_args: [
      '-I' + meson.source_root() + '/sw/host/vendor/mpsse',
      # TODO: Remove this once https://github.com/lowRISC/opentitan/issues/3182
      # is resolved.
      '-Wno-error=deprecated-declarations',
    ],
    dependencies: [
      dependency('libftdi1', native: true),
      dependency('libusb-1.0', native: true),
    ],
    native: true,
  ),
)
