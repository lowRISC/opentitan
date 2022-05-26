# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

subdir('vendor')

rom_ext_signer = custom_target(
  'rom_ext_signer_bazel',
  command: [
    'env', 'PWD_OVERRIDE=' + meson.project_source_root(),
    meson.project_source_root() / 'ci/bazelisk.sh', 'build',
    '//sw/host/rom_ext_image_tools/signer:rom_ext_signer',
  ],
  output: 'nothing',
  build_always_stale: true,
  build_by_default: true,
)

rom_ext_signer_export = custom_target(
  'rom_ext_signer_export',
  command: ['cp', meson.project_source_root() / 'bazel-bin/sw/host/rom_ext_image_tools/signer/rom_ext_signer', '@OUTPUT@'],
  input: rom_ext_signer,
  output: 'rom_ext_signer',
  build_always_stale: true,
  build_by_default: true,
)
