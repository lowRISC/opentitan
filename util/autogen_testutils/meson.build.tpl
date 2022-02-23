# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

${autogen_banner}

# ISR test utilities
sw_lib_testing_isr_testutils = declare_dependency(
  link_with: static_library(
    'sw_lib_testing_isr_testutils',
    sources: ['isr_testutils.c'],
    dependencies: [
% for ip in ips_with_difs:
  % if ip.irqs:
      sw_lib_dif_${ip.name_snake},
  % endif
% endfor
    ],
  ),
)
