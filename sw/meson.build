# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A command, for use in custom_target(), to build artifacts into $BIN_DIR.
export_target_command = [
  meson.source_root() / 'util/export_target.sh',
  bin_dir / 'sw',
  'sw',
  '@OUTDIR@',
  '@INPUT@',
]
export_target_depend_files = [
  meson.source_root() / 'util/export_target.sh',
]

subdir('vendor')
subdir('otbn')
subdir('host')
subdir('device')
