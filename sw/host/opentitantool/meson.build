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

# CARGO FMT FLAGS:
# These flags will only be used for checking code formatting
cargo_fmt_flags_array = [
  'verbose',
  'all',
  'manifest-path=' + manifest_path,
  'check',
]

cargo_fmt_flag = ''
foreach flag : cargo_fmt_flags_array
  cargo_fmt_flag += '--' + flag + ' '
endforeach

# RUSTFLAGS:
# These flags will apply to all the dependencies, as well as the final
# binary. Linker and linker flavor amongst other things can be passed through
# these flags.
rust_flags = ''

# The cargo invocation script.
cargo_invoke_cmd = meson.project_source_root() / 'util/invoke_cargo.sh'

# Note: the opentitantool depends on opentitanlib. This dependency is handled
# by cargo itself but perhaps should be handled by the build system.
opentitantool = custom_target(
  'opentitantool',
  command: [
    cargo_invoke_cmd,
    cargo,
    cargo_flags,
    cargo_fmt_flag,
    rust_flags,
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

opentitantool_export = custom_target(
  'opentitantool_export',
  command: ['cp', '@INPUT@' / build_type / 'opentitantool', '@OUTPUT@'],
  input: opentitantool,
  output: 'opentitantool',
  build_always_stale: true,
  build_by_default: true,
)
