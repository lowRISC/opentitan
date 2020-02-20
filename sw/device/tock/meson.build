# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cargo = find_program('cargo', required: false)

target = 'riscv32imc-unknown-none-elf'
build_type = 'release'

tock_board_dir = meson.source_root() / 'sw/device/tock/boards/opentitan'
toolchain_file = tock_board_dir / 'rust-toolchain'
manifest_path = tock_board_dir / 'Cargo.toml'

# Used to choose local or upstream Tock OS dependencies.
tock_deps_path = meson.source_root() / 'sw/device/tock/tock'
tock_deps_manifest = tock_deps_path / 'Cargo.toml'

rust_flags = '-C link-arg=-Tlayout.ld ' + \
'-C linker=rust-lld ' + \
'-C linker-flavor=ld.lld ' + \
'-C relocation-model=dynamic-no-pic ' + \
'-C link-arg=-zmax-page-size=512'

build_tock_cmd = meson.source_root() / 'util/build_tock.sh'

if tock_local
  run_command('ln', '-s', '-f', tock_deps_path / 'Cargo_local.toml', tock_deps_manifest)
else
  run_command('ln', '-s', '-f', tock_deps_path / 'Cargo_remote.toml', tock_deps_manifest)
endif

tock_raw = custom_target(
  'tock_raw',
  command: [
    build_tock_cmd,
    target,
    build_type,
    manifest_path,
    '@OUTDIR@',
    toolchain_file,
    meson.source_root(),
    meson.build_root(),
    rust_flags,
  ],
  output: target,
  console: true,
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

