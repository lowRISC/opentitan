# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cargo = find_program('cargo', required: false)

target = 'riscv32imc-unknown-none-elf'
build_type = 'release'

manifest_path = meson.source_root() / 'sw/device/tock/boards/opentitan/Cargo.toml'
toolchain_file = meson.source_root() / 'sw/device/tock/boards/opentitan/rust-toolchain'

rust_flags = '-C link-arg=-Tlayout.ld ' + \
'-C linker=rust-lld ' + \
'-C linker-flavor=ld.lld ' + \
'-C relocation-model=dynamic-no-pic ' + \
'-C link-arg=-zmax-page-size=512'

build_tock_cmd = meson.source_root() / 'util/build_tock.sh'

tock_raw = custom_target(
  'tock_raw',
  command: [
    build_tock_cmd,
    target,
    build_type,
    manifest_path,
    '@OUTDIR@',
    toolchain_file,
    rust_flags,
  ],
  output: target,
  build_always_stale: true,
  build_by_default: false,
)

tock_elf = custom_target(
  'tock_elf',
  command: ['cp', '@INPUT@' / build_type / 'opentitan', '@OUTPUT@'],
  depends: tock_raw,
  input: tock_raw,
  output: 'opentitan.elf',
  build_always_stale: true,
  build_by_default: false,
)

tock_bin = custom_target(
  'tock_bin',
  command: [
    prog_objcopy,
    # Remove .apps section to dramatically reduce binary size.
    '--remove-section', '.apps',
    '-O', 'binary',
    '@INPUT@',
    '@OUTPUT@'
  ],
  depends: tock_elf,
  input: tock_elf,
  output: 'opentitan.bin',
  build_always_stale: true,
  build_by_default: false,
)

custom_target(
  'tock_export',
  command: export_embedded_target,
  input: [tock_elf, tock_bin],
  depends: [tock_elf, tock_bin],
  output: 'tock',
  build_always_stale: true,
  build_by_default: false,
)

