# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# All build targets below in `sw_tests` or `sw_signed_tests` will have names
# starting with `sw/device/tests/<test_name>`. They will not contain the
# subdirectory name (e.g., `sim_dv/`), because the build targets are really
# declared in the for loops in this build file.

partner_dir = get_option('partnerdir')
partner_tests_path = 'sw/device/tests/'

hookfile = join_paths(get_option('partnerdir') , partner_tests_path, 'ip_config_hooks.c')

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
