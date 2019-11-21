# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Arguments for custom_target, for copying a completed host binary into
# the appropriate location under $BIN_DIR.
export_host_target = [
  meson.source_root() / 'util/export_target.sh',
  host_bin_dir,
  'sw/host',
  '@OUTDIR@',
  '@INPUT@',
]

subdir('vendor')
subdir('spiflash')
