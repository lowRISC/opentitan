# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
# -o hw/top_englishbreakfast

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
            "//sw/device/lib/dif:aon_timer",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:gpio",
            "//sw/device/lib/dif:pwrmgr",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/dif:spi_device",
            "//sw/device/lib/dif:spi_host",
            "//sw/device/lib/dif:uart",
            "//sw/device/lib/dif:usbdev",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for min in range(0, 8, 10)
]

test_suite(
    name = "plic_all_irqs_test",
    tests = [
        "plic_all_irqs_test_0",
    ],
)

opentitan_test(
    name = "alert_test",
    srcs = ["alert_test.c"],
    # TODO(#22871): Remove "broken" tag once the tests are fixed.
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {
            "//hw/top_earlgrey:fpga_cw310_test_rom": None,
            "//hw/top_earlgrey:fpga_cw310_sival": None,
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:boot_stage",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
