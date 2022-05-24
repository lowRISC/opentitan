# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals})
%>\
# IP Integration Tests
plic_all_irqs_test_lib = declare_dependency(
  link_with: static_library(
    'plic_all_irqs_test_lib',
    sources: [
      'plic_all_irqs_test.c',
    ],
    dependencies: [
      sw_lib_irq,
      sw_lib_mmio,
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
      sw_lib_dif_${n},
% endfor
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

alert_test_lib = declare_dependency(
  link_with: static_library(
    'alert_test_lib',
    sources: [hw_ip_alert_handler_reg_h,
    'alert_test.c'],
    dependencies: [
      sw_lib_mem,
      sw_lib_mmio,
      sw_lib_testing_alert_handler_testutils,
      sw_lib_dif_rv_plic,
      sw_lib_runtime_log,
      sw_lib_testing_test_status,
% for n in sorted(alert_peripheral_names):
      sw_lib_dif_${n},
% endfor
    ],
  ),
)
sw_tests += {
  'alert_test': {
    'library': alert_test_lib,
  }
}
