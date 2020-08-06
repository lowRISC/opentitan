# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

vendor_coremark_base_files = files([
  'eembc_coremark/core_list_join.c',
  'eembc_coremark/core_main.c',
  'eembc_coremark/core_matrix.c',
  'eembc_coremark/core_state.c',
  'eembc_coremark/core_util.c',
])

# googletest and googlemock build definitions
#
# The following is inspired by the meson configuration available in
# https://github.com/mesonbuild/gtest/tree/1.10.0 (which is MIT
# licensed).
thread_dep = dependency('threads')
sw_vendor_gtest_dir = 'google_googletest'

sw_vendor_gtest_googletest_dir = sw_vendor_gtest_dir / 'googletest'
sw_vendor_gtest_googletest_inc_dir = include_directories(
  sw_vendor_gtest_googletest_dir / 'include',
  sw_vendor_gtest_googletest_dir,
  is_system: true,
)
sw_vendor_gtest_googletest_libsources = files(sw_vendor_gtest_googletest_dir / 'src/gtest-all.cc')

sw_vendor_gtest_googlemock_dir = sw_vendor_gtest_dir / 'googlemock'
sw_vendor_gtest_googlemock_inc_dir = include_directories(
  sw_vendor_gtest_googlemock_dir / 'include',
  sw_vendor_gtest_googlemock_dir,
  is_system: true,
)
sw_vendor_gtest_googlemock_libsources = files(sw_vendor_gtest_googlemock_dir / 'src/gmock-all.cc')
sw_vendor_gtest_googlemock_mainsources = files(sw_vendor_gtest_googlemock_dir / 'src/gmock_main.cc')

sw_vendor_gtest = declare_dependency(
  include_directories: [
    sw_vendor_gtest_googletest_inc_dir,
    sw_vendor_gtest_googlemock_inc_dir,
  ],
  sources: [
    sw_vendor_gtest_googletest_libsources,
    sw_vendor_gtest_googlemock_libsources,
    sw_vendor_gtest_googlemock_mainsources,
  ],
  dependencies: thread_dep,
)
# End googletest and googlemock build definitions

# libclang_rt.profile build definitions
sw_vendor_llvm_clang_rt_dir = 'llvm_clang_rt_profile' / 'compiler-rt'
sw_vendor_llvm_clang_rt_profile_dir = sw_vendor_llvm_clang_rt_dir / 'lib' / 'profile'
sw_vendor_llvm_clang_rt_inc_dir = include_directories(
  sw_vendor_llvm_clang_rt_dir / 'include',
)
sw_vendor_llvm_clang_rt_sources = [
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingBiasVar.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingBuffer.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfiling.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingInternal.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingMerge.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingPlatformOther.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingVersionVar.c'),
  files(sw_vendor_llvm_clang_rt_profile_dir / 'InstrProfilingWriter.c'),
]
