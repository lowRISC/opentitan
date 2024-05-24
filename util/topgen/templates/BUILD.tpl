# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
import topgen.lib as lib

alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals})
default_interrupt_domain = lib.get_default_interrupt_domain(top)
%>\
load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

% for interrupt_domain in top["interrupt_domains"]:
<%
intr_domain = interrupt_domain["name"]
plic_suffix = "_" + intr_domain if intr_domain != default_interrupt_domain else ""
plic_name = "rv_plic" + plic_suffix
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals[intr_domain]}) + [plic_name]
%>\
# IP Integration Tests
opentitan_functest(
    name = "plic_all_irqs${plic_suffix}_test",
    srcs = ["plic_all_irqs${plic_suffix}_test.c"],
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
% for n in sorted(irq_peripheral_names):
        "//sw/top_${top["name"]}/sw/dif:${n}",
% endfor
        "//sw/top_${top["name"]}/sw/test/utils:rv_plic${plic_suffix}_testutils",
    ],
)
% endfor

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
