# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

sw_lib_testing_gtest_src_dir = meson.source_root() / 'sw/vendor/google_googletest'
sw_lib_testing_gtest_lock_file = meson.source_root() / 'sw/vendor/google_googletest.lock.hjson'
# Build dir below is $REPO_TOP/build-out/sw/fpga/sw/device/lib/testing/google_googletest
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

build_gtest = custom_target(
  'googletest',
  output: sw_lib_testing_empty_file_for_dep,
  depend_files: sw_lib_testing_gtest_lock_file,
  command: ['bash', '-c', build_gtest_cmd],
)

gtest_inc = include_directories(
  '../../../vendor/google_googletest/googletest/include',
  '../../../vendor/google_googletest/googlemock/include',
)

gtest = declare_dependency(
  sources: [build_gtest],
  include_directories: gtest_inc,
  link_args: [
    '-L' + sw_lib_testing_gtest_build_dir / 'lib',
    '-lgmock',
    '-lgmock_main',
    '-lgtest',
  ],
  dependencies: dependency('threads'),
)
