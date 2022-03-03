# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All build targets below will be built in closed source environment only. 
# In order to build these targets, 'build_closed_source' and 'closed_source_dir'
# build flags should be defined.

closed_source_dir = get_option('closed_source_dir')
closed_source_test_path = 'sw/device/tests/'

hookfile = join_paths(closed_source_dir , closed_source_test_path, \
                      'ip_config_hooks.c')

###############################################################################
# Closed source test libraries.
###############################################################################
closed_source_config_hooks_lib = static_library(
  'closed_source_config_hooks_lib',
  sources: [hookfile],
  dependencies: [
    sw_lib_runtime_log,
  ],
)
closed_source_config_hooks_dep = declare_dependency(
  link_with: closed_source_config_hooks_lib,
)

###############################################################################
# Closed source test.
###############################################################################
sw_tests += {
  'closed_entropy_src_smoketest': {
    'library': entropy_src_smoketest_lib,
    'link_with_closed_configs': true,
  }
}
