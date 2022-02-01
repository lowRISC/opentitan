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
cargo_invoke_cmd = meson.project_source_root() / 'util/invoke_cargo.sh'

# Get the command lines for the native C and C++ compilers to pass on to other
# build systems.
# The Mundane rust library uses CMake to build BoringSSL, which needs a native
# C/C++ compiler. Ensure that this build step uses the same native compiler as
# all other parts of the build.
prog_c_native = ' '.join(meson.get_compiler('c', native: true).cmd_array())
prog_cxx_native = ' '.join(meson.get_compiler('cpp', native: true).cmd_array())

rom_ext_signer = custom_target(
  'rom_ext_signer',
  command: [
    prog_env,
    'CC=@0@'.format(prog_c_native),
    'CXX=@0@'.format(prog_cxx_native),
    cargo_invoke_cmd,
    cargo,
    cargo_flags,
    rust_flags,
    '',
    meson.project_source_root(),
    meson.project_build_root(),
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
