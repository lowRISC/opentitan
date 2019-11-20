# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# RISC-V linker parameters.
riscv_linker_script = '@0@/@1@'.format(meson.source_root(), files(['link.ld'])[0])
riscv_linker_args = [
  '-Wl,-T,@0@'.format(riscv_linker_script),
  # Ensure we don't include a build-id attribute in the ELF.
  '-Wl,--build-id=none',
]

# RISC-V startup library. Every RISC-V executable should depend on this target.
riscv_crt = declare_dependency(
  link_args: riscv_linker_args,
  link_with: static_library(
    'riscv_crt',
    sources: ['_crt.c'],
    # NOTE: This line is mostly to make sure that a change in link.ld causes a
    # recompilation.
    link_depends: [riscv_linker_script],
  ),
)
