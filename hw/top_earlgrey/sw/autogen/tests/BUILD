# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
# -o hw/top_earlgrey

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

# Number of periphals per test
NR_IRQ_PERIPH_PER_TEST = 10

# Total numbers of tests (the last will contain only remaining IRQs)
NR_IRQ_PERIPH_TESTS = 3

[
    opentitan_test(
        name = "plic_all_irqs_test_{}".format(idx * NR_IRQ_PERIPH_PER_TEST),
        srcs = ["plic_all_irqs_test.c"],
        # For the last test, do not specify TEST_MAX_IRQ_PERIPHERAL to be sure
        # that we are capturing all peripherals.
        copts = [
            "-DTEST_MIN_IRQ_PERIPHERAL={}".format(idx * NR_IRQ_PERIPH_PER_TEST),
        ] + ([
            "-DTEST_MAX_IRQ_PERIPHERAL={}".format((idx + 1) * NR_IRQ_PERIPH_PER_TEST),
        ] if idx < NR_IRQ_PERIPH_PER_TEST - 1 else []),
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
            "//sw/device/lib/dif/autogen:adc_ctrl",
            "//sw/device/lib/dif/autogen:alert_handler",
            "//sw/device/lib/dif/autogen:aon_timer",
            "//sw/device/lib/dif/autogen:csrng",
            "//sw/device/lib/dif/autogen:edn",
            "//sw/device/lib/dif/autogen:entropy_src",
            "//sw/device/lib/dif/autogen:flash_ctrl",
            "//sw/device/lib/dif/autogen:gpio",
            "//sw/device/lib/dif/autogen:hmac",
            "//sw/device/lib/dif/autogen:i2c",
            "//sw/device/lib/dif/autogen:keymgr",
            "//sw/device/lib/dif/autogen:kmac",
            "//sw/device/lib/dif/autogen:otbn",
            "//sw/device/lib/dif/autogen:otp_ctrl",
            "//sw/device/lib/dif/autogen:pattgen",
            "//sw/device/lib/dif/autogen:pwrmgr",
            "//sw/device/lib/dif/autogen:rv_plic",
            "//sw/device/lib/dif/autogen:rv_timer",
            "//sw/device/lib/dif/autogen:sensor_ctrl",
            "//sw/device/lib/dif/autogen:spi_device",
            "//sw/device/lib/dif/autogen:spi_host",
            "//sw/device/lib/dif/autogen:sysrst_ctrl",
            "//sw/device/lib/dif/autogen:uart",
            "//sw/device/lib/dif/autogen:usbdev",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for idx in range(NR_IRQ_PERIPH_TESTS)
]

test_suite(
    name = "plic_all_irqs_test",
    tests = [
        "plic_all_irqs_test_{}".format(idx * NR_IRQ_PERIPH_PER_TEST)
        for idx in range(NR_IRQ_PERIPH_TESTS)
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
        "//sw/device/lib/dif/autogen:adc_ctrl",
        "//sw/device/lib/dif/autogen:aes",
        "//sw/device/lib/dif/autogen:alert_handler",
        "//sw/device/lib/dif/autogen:aon_timer",
        "//sw/device/lib/dif/autogen:clkmgr",
        "//sw/device/lib/dif/autogen:csrng",
        "//sw/device/lib/dif/autogen:edn",
        "//sw/device/lib/dif/autogen:entropy_src",
        "//sw/device/lib/dif/autogen:flash_ctrl",
        "//sw/device/lib/dif/autogen:gpio",
        "//sw/device/lib/dif/autogen:hmac",
        "//sw/device/lib/dif/autogen:i2c",
        "//sw/device/lib/dif/autogen:keymgr",
        "//sw/device/lib/dif/autogen:kmac",
        "//sw/device/lib/dif/autogen:lc_ctrl",
        "//sw/device/lib/dif/autogen:otbn",
        "//sw/device/lib/dif/autogen:otp_ctrl",
        "//sw/device/lib/dif/autogen:pattgen",
        "//sw/device/lib/dif/autogen:pinmux",
        "//sw/device/lib/dif/autogen:pwm",
        "//sw/device/lib/dif/autogen:pwrmgr",
        "//sw/device/lib/dif/autogen:rom_ctrl",
        "//sw/device/lib/dif/autogen:rstmgr",
        "//sw/device/lib/dif/autogen:rv_core_ibex",
        "//sw/device/lib/dif/autogen:rv_plic",
        "//sw/device/lib/dif/autogen:rv_timer",
        "//sw/device/lib/dif/autogen:sensor_ctrl",
        "//sw/device/lib/dif/autogen:spi_device",
        "//sw/device/lib/dif/autogen:spi_host",
        "//sw/device/lib/dif/autogen:sram_ctrl",
        "//sw/device/lib/dif/autogen:sysrst_ctrl",
        "//sw/device/lib/dif/autogen:uart",
        "//sw/device/lib/dif/autogen:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
