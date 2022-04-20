# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('drivers')

# OTBN interface
sw_lib_crypto_otbn_util = declare_dependency(
  link_with: static_library(
    'sw_lib_crypto_otbn_util',
    sources: [
      'otbn_util.c',
    ],
    dependencies: [
      sw_lib_crypto_otbn,
    ]
  )
)

# Setup for building OTBN assembly. OTBN software is build with a separate
# toolchain, which is called as an external target from Meson in
# subdirectories.

prog_otbn_build = meson.project_source_root() / 'util/otbn_build.py'

otbn_build_command = [
  prog_env,
  'OTBN_TOOLS=@0@'.format(path_otbn_tools),
  'OTBN_LD=@0@'.format(prog_otbn_ld),
  'RV32_TOOL_OBJCOPY=@0@'.format(prog_objcopy.full_path()),
  'RV32_TOOL_AS=@0@'.format(prog_as.full_path()),
  'RV32_TOOL_LD=@0@'.format(prog_ld.full_path()),
  prog_python,
  prog_otbn_build,
  '--out-dir',
  '@OUTDIR@',
  '@INPUT@',
]
otbn_build_depend_files = [
  prog_otbn_as,
  prog_otbn_ld,
  prog_objcopy.full_path(),
  prog_as.full_path(),
  prog_ld.full_path(),
  prog_otbn_build,
]

# Subdirectories with OTBN files or dependencies must come after the OTBN setup.

subdir('ecdsa_p256')
subdir('rsa_3072')
