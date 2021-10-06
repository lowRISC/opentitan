# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
enabled_peripherals = ['aes', 'alert_handler', 'clkmgr', 'csrng', 'edn',
                       'entropy_src', 'gpio', 'hmac', 'i2c', 'keymgr',
                       'lc_ctrl', 'otbn', 'otp_ctrl', 'pwrmgr', 'rstmgr',
                       'sram_ctrl',  'uart']
parameterized_peripherals = ['alert_handler']
%>\
# IP Integration Tests
plic_all_irqs_test_lib = declare_dependency(
  link_with: static_library(
    'plic_all_irqs_test_lib',
    sources: [
% for p in parameterized_peripherals:
      hw_ip_${p}_reg_h,
% endfor
      'plic_all_irqs_test.c',
    ],
    dependencies: [
% for p in irq_peripheral_names:
<%
      if p not in enabled_peripherals:
          continue
%>\
      sw_lib_dif_${p},
% endfor
      sw_lib_dif_rv_plic,
      sw_lib_irq,
      sw_lib_mmio,
      sw_lib_runtime_log,
      sw_lib_testing_rv_plic_testutils,
      sw_lib_testing_test_status,
      top_earlgrey,
    ],
  ),
)
sw_tests += {
  'plic_all_irqs_test': {
    'library': plic_all_irqs_test_lib,
  }
}
