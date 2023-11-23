# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
# -o hw/top_earlgrey

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
            "//sw/device/lib/dif:adc_ctrl",
            "//sw/device/lib/dif:alert_handler",
            "//sw/device/lib/dif:aon_timer",
            "//sw/device/lib/dif:csrng",
            "//sw/device/lib/dif:edn",
            "//sw/device/lib/dif:entropy_src",
            "//sw/device/lib/dif:flash_ctrl",
            "//sw/device/lib/dif:gpio",
            "//sw/device/lib/dif:hmac",
            "//sw/device/lib/dif:i2c",
            "//sw/device/lib/dif:keymgr",
            "//sw/device/lib/dif:kmac",
            "//sw/device/lib/dif:otbn",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:pattgen",
            "//sw/device/lib/dif:pwrmgr",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/dif:rv_timer",
            "//sw/device/lib/dif:sensor_ctrl",
            "//sw/device/lib/dif:spi_device",
            "//sw/device/lib/dif:spi_host",
            "//sw/device/lib/dif:sysrst_ctrl",
            "//sw/device/lib/dif:uart",
            "//sw/device/lib/dif:usbdev",
            "//sw/device/lib/runtime:irq",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:rv_plic_testutils",
            "//sw/device/lib/testing/test_framework:ottf_main",
        ],
    )
    for min in range(0, 23, 10)
]

test_suite(
    name = "plic_all_irqs_test",
    tests = [
        "plic_all_irqs_test_0",
        "plic_all_irqs_test_10",
        "plic_all_irqs_test_20",
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
