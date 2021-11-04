# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################
# (Current) On-device Test Framework
###############################################################################
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

sw_lib_testing_test_main = declare_dependency(
  link_with: static_library(
    'test_main_ot',
    sources: ['test_main.c'],
    dependencies: [
      sw_lib_runtime_log,
      sw_lib_runtime_print,
      sw_lib_dif_uart,
      sw_lib_testing_test_status,
      sw_lib_testing_test_coverage,
    ],
  )
)

###############################################################################
# (Future) On-device Test Framework (OTTF)
# See #8015: https://github.com/lowRISC/opentitan/issues/8015
###############################################################################
# FreeRTOS kernel paths.
freertos_root = '@0@/@1@'.format(meson.source_root(), 'sw/vendor/freertos_freertos_kernel')
freertos_memmang_path = '@0@/@1@'.format(freertos_root, 'portable/MemMang')
freertos_portable_path = '@0@/@1@'.format(freertos_root, 'portable/GCC/RISC-V')

# OpenTitan Test Framework (OTTF) sources & includes.
ottf_sources = [
  'ottf.c',
  'ottf_isrs.c',
  'example_ottf_test.c',
  'freertos_hooks.c',
  'freertos_port.S',
  'freertos_port.c',
  hw_ip_rv_timer_reg_h,
  join_paths(freertos_root ,'tasks.c'),
  join_paths(freertos_root ,'queue.c'),
  join_paths(freertos_root ,'list.c'),
  join_paths(freertos_memmang_path,'heap_1.c'),
]
ottf_incdirs = include_directories(
  '../../../../vendor/freertos_freertos_kernel/include',
  '../../../../vendor/freertos_freertos_kernel/portable/GCC/RISC-V')

# OpenTitan Test Framework (OTTF)
sw_lib_ottf = declare_dependency(
  link_with: static_library(
    'sw_lib_ottf',
    sources: ottf_sources,
    include_directories: ottf_incdirs,
    c_args: [
      '-D__riscv_float_abi_soft',
    ],
    dependencies: [
      sw_lib_mem,
      sw_lib_runtime_ibex,
      sw_lib_runtime_hart,
      sw_lib_runtime_log,
      sw_lib_runtime_print,
      sw_lib_irq,
      sw_lib_dif_uart,
      sw_lib_dif_rv_timer,
      sw_lib_testing_test_status,
      sw_lib_testing_test_coverage,
    ],
  )
)
