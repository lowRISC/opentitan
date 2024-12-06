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
load("//rules:autogen.bzl", "opentitan_autogen_tests")
load("@bazel_skylib//lib:dicts.bzl", "dicts")

package(default_visibility = ["//visibility:public"])

opentitan_autogen_tests(
    name = "autogen",
    top = "//hw/top:top_desc",
)

# Number of peripherals per test.
NR_IRQ_PERIPH_PER_TEST = 10

# Total numbers of tests (the last one will contain but remaining IRQs).
NR_IRQ_PERIPH_TESTS = 3

[
    opentitan_test(
        name = "plic_all_irqs_test_{}".format(idx),
        srcs = [":autogen_plic_all_irqs_test_src"],
        # For the last test, we do not specify TEST_MAX_IRQ_PERIPHERAL so
        # we are sure to capture all peripherals.
        copts = [
            "-DTEST_MIN_IRQ_PERIPHERAL={}".format(idx * NR_IRQ_PERIPH_PER_TEST),
        ] + ([
            "-DTEST_MAX_IRQ_PERIPHERAL={}".format((idx + 1) * NR_IRQ_PERIPH_PER_TEST),
        ] if idx < NR_IRQ_PERIPH_TESTS - 1 else []),
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
            "//hw/top:top_lib",
            "//sw/device/lib/arch:boot_stage",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:all_difs",
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
        "plic_all_irqs_test_{}".format(idx)
        for idx in range(NR_IRQ_PERIPH_TESTS)
    ],
)

opentitan_test(
    name = "alert_test",
    srcs = [":autogen_alert_test_src"],
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
        "//hw/top:top_lib",
        "//sw/device/lib/arch:boot_stage",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:adc_ctrl",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/dif:alert_handler",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:clkmgr",
        "//sw/device/lib/dif:csrng",
        "//sw/device/lib/dif:edn",
        "//sw/device/lib/dif:entropy_src",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:hmac",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:pattgen",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:pwm",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:sensor_ctrl",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/dif:sysrst_ctrl",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/dif:usbdev",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:alert_handler_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
