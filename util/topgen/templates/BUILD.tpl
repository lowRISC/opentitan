# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals})
%>\
load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

# IP Integration Tests
opentitan_functest(
    name = "plic_all_irqs_test",
    srcs = ["plic_all_irqs_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["broken"],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/base:mmio",
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
        "//sw/device/lib/dif:${n}",
% endfor
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_functest(
    name = "alert_test",
    srcs = ["alert_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
% for n in sorted(alert_peripheral_names + ["alert_handler"]):
        "//sw/device/lib/dif:${n}",
% endfor
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
