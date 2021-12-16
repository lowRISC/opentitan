# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Test status library.
sw_lib_testing_test_status = declare_dependency(
  link_with: static_library(
    'test_status_ot',
    sources: ['test_status.c'],
    dependencies: [
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_runtime_hart,
    ],
  )
)

# NOP coverage dependencies when coverage is not enabled.
sw_lib_testing_test_coverage = declare_dependency(
  link_with: static_library(
    'test_coverage_none',
    sources: [files('test_coverage_none.c')],
  ),
)
collect_coverage = declare_dependency()

if coverage
  # Test coverage library that provides runtime functions for LLVM profiling.
  sw_lib_testing_test_coverage = declare_dependency(
    link_with: static_library(
      'test_coverage_llvm',
      include_directories: sw_vendor_llvm_clang_rt_inc_dir,
      sources: [
        sw_vendor_llvm_clang_rt_sources,
        files('test_coverage_llvm.c'),
      ],
      dependencies: [
        sw_lib_mem,
        sw_lib_dif_uart,
        sw_lib_runtime_log,
      ],
    ),
  )

  # Dependency for enabling coverage
  collect_coverage = declare_dependency(
    compile_args: ['-fprofile-instr-generate', '-fcoverage-mapping'],
    dependencies: sw_lib_testing_test_coverage,
  )
endif

# OTTF (Default) Interrupt Service Routines
#
# ottf_isrs.c contains various definitions with weak linkage, for interrupt
# service routine (ISR) symbols referenced from test_rom_ext.
#
# To override any default ISRs, implement the declarations in ottf_isrs.h,
# you intend to override, and link this library or the OTTF below (depending if
# your tests intends to make use of the OTTF or not).
sw_lib_testing_ottf_isrs = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_ottf_isrs',
    sources: [
      'ottf_isrs.c',
      'ottf_isrs.S',
    ],
    dependencies: [
      sw_lib_mem,
      sw_lib_runtime_hart,
      sw_lib_runtime_ibex,
      sw_lib_runtime_log,
    ],
  )
)

# OpenTitan Test Framework (OTTF)
freertos_root = '@0@/@1@'.format(meson.source_root(), 'sw/vendor/freertos_freertos_kernel')
freertos_memmang_path = '@0@/@1@'.format(freertos_root, 'portable/MemMang')
freertos_portable_path = '@0@/@1@'.format(freertos_root, 'portable/GCC/RISC-V')
ottf_incdirs = include_directories(
  '../../../../vendor/freertos_freertos_kernel/include',
  '../../../../vendor/freertos_freertos_kernel/portable/GCC/RISC-V')
sw_lib_testing_ottf = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_ottf',
    sources: [
      'ottf.c',
      'freertos_hooks.c',
      'freertos_port.S',
      'freertos_port.c',
      join_paths(freertos_root ,'tasks.c'),
      join_paths(freertos_root ,'queue.c'),
      join_paths(freertos_root ,'list.c'),
      join_paths(freertos_memmang_path,'heap_1.c'),
    ],
    include_directories: ottf_incdirs,
    c_args: [
      '-D__riscv_float_abi_soft',
    ],
    dependencies: [
      sw_lib_irq,
      sw_lib_mem,
      sw_lib_dif_uart,
      sw_lib_dif_rv_timer,
      sw_lib_runtime_log,
      sw_lib_runtime_print,
      sw_lib_testing_ottf_isrs,
      sw_lib_testing_test_status,
      sw_lib_testing_test_coverage,
    ],
  )
)
