# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gencmd.replace("//", "#")}

<%
import topgen.lib as lib

## TODO: Darjeeling contains peripherals which expose IRQs/Alerts to the RV
## PLIC and Alert Handler respectively, but are not accessible from the hart
## address space and thus cannot be tested directly (via the IRQ_TEST and
## ALERT_TEST registers). While this issue remains, we specifically hard-code
## for excluding these IRQs/Alerts from the tests.
IGNORE_PERIPHERALS = [("ac_range_check", "darjeeling"), ("racl_ctrl", "darjeeling")]
irq_peripheral_names = sorted({p.name for p in helper.irq_peripherals[addr_space]
                               if (p.inst_name, top["name"]) not in IGNORE_PERIPHERALS})
has_alert_handler = lib.find_module(top['module'], 'alert_handler')
alert_peripheral_names = sorted({p.name for p in helper.alert_peripherals[addr_space]
                                 if (p.inst_name, top["name"]) not in IGNORE_PERIPHERALS
                                }) if has_alert_handler else []

## Collect the execution environments based on the target top-level
if top["name"] == "earlgrey":
    exec_envs = [
        "EARLGREY_TEST_ENVS",
        "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ]
elif top["name"] == "darjeeling":
    exec_envs = [{"//hw/top_darjeeling:sim_dv": None}]
else:
    exec_envs = []

defs_imports = sorted(
    [env for env in exec_envs if isinstance(env, str)] + [
        "cw310_params",
        "fpga_params",
        "opentitan_test",
        "silicon_params",
        "verilator_params",
    ]
)
%>\
load(
    "//rules/opentitan:defs.bzl",
% for imp in defs_imports:
    "${imp}",
% endfor
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
% for exec_env in exec_envs:
% if isinstance(exec_env, str):
            ${exec_env},
% else:
            {
% for k, v in exec_env.items():
                "${k}": ${'"{}"'.format(v) if v else None},
% endfor
            },
% endif
% endfor
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
            "//hw/top_${top["name"]}/sw/autogen:top_${top["name"]}",
            "//sw/device/lib/arch:boot_stage",
            "//sw/device/lib/base:mmio",
% for n in sorted(irq_peripheral_names + ["rv_plic"]):
            "//sw/device/lib/dif/autogen:${n}",
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
% for exec_env in exec_envs:
% if isinstance(exec_env, str):
        ${exec_env},
% else:
        {
% for k, v in exec_env.items():
            "${k}": ${'"{}"'.format(v) if v else None},
% endfor
        },
% endif
% endfor
    ),
    deps = [
        "//hw/top_${top["name"]}/sw/autogen:top_${top["name"]}",
        "//sw/device/lib/arch:boot_stage",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
% for n in sorted(alert_peripheral_names + ["alert_handler"]):
        "//sw/device/lib/dif/autogen:${n}",
% endfor
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
