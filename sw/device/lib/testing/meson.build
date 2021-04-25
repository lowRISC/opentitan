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
