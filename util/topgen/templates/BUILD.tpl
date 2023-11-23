# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals})
%>\
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
    "verilator_params",
)

# IP Integration Tests
[
    opentitan_test(
        name = "plic_all_irqs_test_{}".format(min),
        srcs = ["plic_all_irqs_test.c"],
        copts = [
            "-DTEST_MIN_IRQ_PERIPHERAL={}".format(min),
            "-DTEST_MAX_IRQ_PERIPHERAL={}".format(min + 10),
        ],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:sim_dv": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
        verilator = verilator_params(
            timeout = "eternal",
            tags = ["flaky"],
            # often times out in 3600s on 4 cores
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
            "//sw/device/lib/dif:${n}",
% endfor
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for min in range(0, ${len(irq_peripheral_names)}, 10)
]

test_suite(
    name = "plic_all_irqs_test",
    tests = [
## Use template loop instead of Starlark loop here to be able to easily detect
## if number of tests have changed (so DV files can be updated accordingly)
% for min in range(0, len(irq_peripheral_names), 10):
        "plic_all_irqs_test_${min}",
% endfor
    ],
)

opentitan_test(
    name = "alert_test",
    srcs = ["alert_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
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
