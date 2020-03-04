# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('lib')
subdir('exts')

# Arguments for custom_target, for converting a linked .elf file into .bin and .vmem
# files (plus a disassembled .dis file).
#
# These definitions should only be available to directories which define executables.
make_embedded_target_outputs = ['@BASENAME@.bin', '@BASENAME@.dis', '@BASENAME@.vmem']
make_embedded_target = [
  prog_python, meson.source_root() / 'util/embedded_target.py',
  '--objcopy', prog_objcopy,
  '--srec_cat', prog_srec_cat,
  '--objdump', prog_objdump,
  '--input', '@INPUT@',
  '--basename', '@BASENAME@',
  '--outdir', '@OUTDIR@',
]

# Arguments for custom_target, for copying a completed |make_embedded_target| into
# the appropriate location under $BIN_DIR.
export_embedded_target = [
  meson.source_root() / 'util/export_target.sh',
  dev_bin_dir,
  'sw/device',
  '@OUTDIR@',
  '@INPUT@',
]

subdir('boot_rom')
subdir('examples')
subdir('tests')
subdir('benchmarks')
