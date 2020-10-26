# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cargo = find_program('cargo', required: false, disabler: true)

target = 'riscv32imc-unknown-none-elf'
build_type = 'release'
build_dir = meson.current_build_dir()

tock_board_dir = meson.current_source_dir() / 'boards/opentitan'
toolchain_file = tock_board_dir / 'rust-toolchain'
manifest_path = tock_board_dir / 'Cargo.toml'

# Used to choose local or upstream Tock OS dependencies.
tock_deps_path = meson.current_source_dir() / 'tock'
tock_deps_manifest = tock_deps_path / 'Cargo.toml'

# CARGO FLAGS:
# These flags will only apply to the final binary, and won't get propogated
# to the dependency crate builds.
cargo_flags_array = [
  'manifest-path=' + manifest_path,
  'target-dir=' + build_dir,
  'target=' + target,
   build_type,
]

cargo_flags = ''
foreach flag : cargo_flags_array
  cargo_flags += '--' + flag + ' '
endforeach

# RUSTFLAGS:
# These flags will apply to all the dependencies, as well as the final
# binary. Linker and linker flavor amongst other things can be passed through
# these flags.
rust_flags = '-C link-arg=-Tlayout.ld ' + \
'-C linker=rust-lld ' + \
'-C linker-flavor=ld.lld ' + \
'-C relocation-model=dynamic-no-pic ' + \
'-C link-arg=-zmax-page-size=512'

# The cargo invocation script.
cargo_invoke_cmd = meson.source_root() / 'util/invoke_cargo.sh'

if tock_local
  run_command('ln', '-s', '-f', tock_deps_path / 'Cargo_local.toml', tock_deps_manifest)
else
  run_command('ln', '-s', '-f', tock_deps_path / 'Cargo_remote.toml', tock_deps_manifest)
endif

tock_raw = custom_target(
  'tock_raw',
  command: [
    cargo_invoke_cmd,
    cargo,
    cargo_flags,
    rust_flags,
    toolchain_file,
    meson.source_root(),
    meson.build_root(),
  ],
  depend_files: [
    cargo_invoke_cmd,
    manifest_path,
    toolchain_file,
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
  input: tock_elf,
  output: 'opentitan.bin',
  build_always_stale: true,
  build_by_default: false,
)

custom_target(
  'tock_export',
  command: export_target_command,
  depend_files: [export_target_depend_files,],
  input: [tock_elf, tock_bin],
  output: 'tock',
  build_always_stale: true,
  build_by_default: false,
)
