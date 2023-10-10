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
    tags = ["earlgrey"],
    targets = [
        "cw310_test_rom",
        "verilator",
        "dv",
    ],
    verilator = verilator_params(
        timeout = "eternal",
        tags = ["flaky"],
        # often times out in 3600s on 4 cores
    ),
    deps = [
        "//hw/top_${top["name"]}/sw/autogen:top_${top["name"]}",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_${top["name"]}/sw/device/runtime:print",
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
        "//sw/top_${top["name"]}/sw/dif:${n}",
% endfor
        "//sw/top_${top["name"]}/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "alert_test",
    srcs = ["alert_test.c"],
    tags = ["earlgrey"],
    deps = [
        "//hw/top_${top["name"]}/sw/autogen:top_${top["name"]}",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_${top["name"]}/sw/device/runtime:print",
% for n in sorted(alert_peripheral_names + ["alert_handler"]):
<%
if top["name"] == "earlgrey" and n == "lc_ctrl_v1":
    n = "lc_ctrl"
%>\
        "//sw/top_${top["name"]}/sw/dif:${n}",
% endfor
        "//sw/top_${top["name"]}/sw/test/utils:alert_handler_testutils",
    ],
)
