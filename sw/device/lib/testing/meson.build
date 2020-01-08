# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_testing_gtest_src_dir = meson.source_root() / 'sw/vendor/google_googletest'
sw_lib_testing_gtest_lock_file = meson.source_root() / 'sw/vendor/google_googletest.lock.hjson'
# Build dir below is $REPO_TOP/build-out/sw/${DEVICE}/sw/device/lib/testing/google_googletest
sw_lib_testing_gtest_build_dir = meson.current_build_dir() / 'google_googletest'
sw_lib_testing_empty_file_for_dep = 'empty_file_for_googletest_dependency.cc'

# Bash script used for building googletest. Also creates an empty file
# which is used to establish the dependency between gtest and mock_mmio.
build_gtest_cmd = '''
echo "Building googletest..."
GTEST_BUILD_DIR="@0@"
GTEST_SRC_DIR="@1@"
EMPTY_FILE_FOR_DEP="@2@"
# Create a directory for building gtest
mkdir -p $GTEST_BUILD_DIR
# Build googletest
cmake -B $GTEST_BUILD_DIR -S $GTEST_SRC_DIR > /dev/null
make -C $GTEST_BUILD_DIR > /dev/null
# Create an empty file for dependencies
touch "@OUTDIR@/$EMPTY_FILE_FOR_DEP"
echo "Done!"
'''.format(sw_lib_testing_gtest_build_dir, sw_lib_testing_gtest_src_dir, sw_lib_testing_empty_file_for_dep)

sw_lib_testing_build_gtest = custom_target(
  'googletest',
  output: sw_lib_testing_empty_file_for_dep,
  depend_files: sw_lib_testing_gtest_lock_file,
  command: ['bash', '-e', '-c', build_gtest_cmd],
  console: true,
)

sw_lib_testing_gtest = declare_dependency(
  sources: [sw_lib_testing_build_gtest],
  link_args: [
    '-L' + sw_lib_testing_gtest_build_dir / 'lib',
    '-lgmock',
    '-lgmock_main',
    '-lgtest',
  ],
  dependencies: dependency('threads'),
  compile_args: [
    # These are necessary in order to make gtest headers correctly find other
    # gtest headers.
    '-I' + meson.source_root() / 'sw/vendor/google_googletest/googletest/include',
    '-I' + meson.source_root() / 'sw/vendor/google_googletest/googlemock/include',
  ],
)

sw_lib_testing_mock_mmio = declare_dependency(
  link_with: static_library(
    'mock_mmio',
    sources: [
      meson.source_root() / 'sw/device/lib/base/mmio.c',
      'mock_mmio.cc',
    ],
    dependencies: [sw_lib_testing_gtest],
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
    sw_lib_testing_gtest,
    sw_lib_testing_mock_mmio,
  ],
  native: true,
  cpp_args: ['-DMOCK_MMIO'],
))
