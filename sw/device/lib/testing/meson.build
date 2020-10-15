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
        sw_lib_uart,
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

sw_lib_testing_bitfield = declare_dependency(
  link_with: static_library(
    'bitfield',
    sources: [
      meson.source_root() / 'sw/device/lib/base/bitfield.c',
    ],
    native: true,
  )
)

sw_lib_testing_mock_mmio = declare_dependency(
  link_with: static_library(
    'mock_mmio',
    sources: [
      meson.source_root() / 'sw/device/lib/base/mmio.c',
      'mock_mmio.cc',
    ],
    dependencies: [
      sw_vendor_gtest,
      sw_lib_testing_bitfield,
    ],
    native: true,
    c_args: ['-DMOCK_MMIO'],
    cpp_args: ['-DMOCK_MMIO'],
  )
)

# Example test using mock_mmio.h, which also serves to
# test that mock_mmio.h works correctly.
test('mock_mmio_test', executable(
  'mock_mmio_test',
  sources: ['mock_mmio_test.cc'],
  dependencies: [
    sw_vendor_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  cpp_args: ['-DMOCK_MMIO'],
))
