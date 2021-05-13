# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

cargo = find_program('cargo', required: false, disabler: true)

build_type = 'release'
build_dir = meson.current_build_dir()
manifest_path = meson.current_source_dir() / 'Cargo.toml'

# CARGO FLAGS:
# These flags will only apply to the final binary, and won't get propogated
# to the dependency crate builds.
cargo_flags_array = [
  'manifest-path=' + manifest_path,
  'target-dir=' + build_dir,
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
rust_flags = ''

# The cargo invocation script.
cargo_invoke_cmd = meson.source_root() / 'util/invoke_cargo.sh'

rom_ext_signer = custom_target(
  'rom_ext_signer',
  command: [
    cargo_invoke_cmd,
    cargo,
    cargo_flags,
    rust_flags,
    '',
    meson.source_root(),
    meson.build_root(),
  ],
  depend_files: [
    cargo_invoke_cmd,
    manifest_path,
  ],
  output: '.',
  console: true,
  build_always_stale: true,
  build_by_default: true,
)

rom_ext_signer_export = custom_target(
  'rom_ext_signer_export',
  command: ['cp', '@INPUT@' / build_type / 'rom_ext_signer', '@OUTPUT@'],
  input: rom_ext_signer,
  output: 'rom_ext_signer',
  build_always_stale: true,
  build_by_default: true,
)
