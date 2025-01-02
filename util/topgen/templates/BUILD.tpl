# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
import topgen.lib as lib

irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals})
has_alert_handler = lib.find_module(top['module'], 'alert_handler')
alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals}) if has_alert_handler else []
%>\
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)
load("@bazel_skylib//lib:dicts.bzl", "dicts")

package(default_visibility = ["//visibility:public"])

[
    opentitan_test(
        name = "plic_all_irqs_test_{}".format(min),
        srcs = ["plic_all_irqs_test.c"],
        copts = [
            "-DTEST_MIN_IRQ_PERIPHERAL={}".format(min),
            "-DTEST_MAX_IRQ_PERIPHERAL={}".format(min + 10),
        ],
        exec_env = dicts.add(
            EARLGREY_TEST_ENVS,
            EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
            {
                "//hw/top_earlgrey:fpga_cw310_test_rom": None,
                "//hw/top_earlgrey:fpga_cw310_sival": None,
                "//hw/top_earlgrey:silicon_creator": None,
            },
        ),
        verilator = verilator_params(
            timeout = "eternal",
            tags = [
                "flaky",
                "manual",
            ],
            # This test can take > 60 minutes, so mark it manual as it
            # shouldn't run in CI/nightlies.
            # often times out in 3600s on 4 cores
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/arch:boot_stage",
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
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:boot_stage",
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
