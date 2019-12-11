# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# RISC-V linker parameters.
riscv_flash_linker_script = '@0@/@1@'.format(meson.source_root(), files(['flash_binary.ld'])[0])
riscv_flash_linker_args = [
  '-Wl,-T,@0@'.format(riscv_flash_linker_script),
  # Depending on the compiler and its configuration (*), |--build-id| is passed
  # to the linker, causing the insertion of a ".note.gnu.build-id" section into
  # the ELF file. We do not use the build ID. Achieve consistent behavior and
  # potentially a small improvement in linking time by not computing the build
  # ID in the first place.
  #
  # * GCC built with |--enable-linker-build-id|, clang before 3.9 or built with
  #   |-DENABLE_LINKER_BUILD_ID|.
  '-Wl,--build-id=none',
]

# RISC-V startup library. Every RISC-V executable should depend on this target.
riscv_flash_crt = declare_dependency(
  link_args: riscv_flash_linker_args,
  # These files provide special sections for the linker script, and, as such,
  # must be provided as object files, not static libraries.
  sources: ['flash_crt.c', 'irq_vector.S'],
  link_with: static_library(
    'riscv_linker_script_dep_shim',
    sources: ['irq.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_uart,
    ],
    link_depends: [riscv_flash_linker_script],
  )
)