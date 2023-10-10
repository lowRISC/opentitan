# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
# -o hw/top_darjeeling

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
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:irq",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:dma",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:keymgr_dpe",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:mbx",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:rv_plic_testutils",
    ],
)

opentitan_functest(
    name = "alert_test",
    srcs = ["alert_test.c"],
    tags = ["earlgrey"],
    deps = [
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:mmio",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/dif:aes",
        "//sw/top_darjeeling/sw/dif:alert_handler",
        "//sw/top_darjeeling/sw/dif:aon_timer",
        "//sw/top_darjeeling/sw/dif:clkmgr",
        "//sw/top_darjeeling/sw/dif:csrng",
        "//sw/top_darjeeling/sw/dif:dma",
        "//sw/top_darjeeling/sw/dif:edn",
        "//sw/top_darjeeling/sw/dif:gpio",
        "//sw/top_darjeeling/sw/dif:hmac",
        "//sw/top_darjeeling/sw/dif:i2c",
        "//sw/top_darjeeling/sw/dif:keymgr_dpe",
        "//sw/top_darjeeling/sw/dif:kmac",
        "//sw/top_darjeeling/sw/dif:lc_ctrl",
        "//sw/top_darjeeling/sw/dif:mbx",
        "//sw/top_darjeeling/sw/dif:otbn",
        "//sw/top_darjeeling/sw/dif:otp_ctrl",
        "//sw/top_darjeeling/sw/dif:pinmux",
        "//sw/top_darjeeling/sw/dif:pwrmgr",
        "//sw/top_darjeeling/sw/dif:rom_ctrl",
        "//sw/top_darjeeling/sw/dif:rstmgr",
        "//sw/top_darjeeling/sw/dif:rv_core_ibex",
        "//sw/top_darjeeling/sw/dif:rv_plic",
        "//sw/top_darjeeling/sw/dif:rv_timer",
        "//sw/top_darjeeling/sw/dif:sensor_ctrl",
        "//sw/top_darjeeling/sw/dif:soc_proxy",
        "//sw/top_darjeeling/sw/dif:spi_device",
        "//sw/top_darjeeling/sw/dif:spi_host",
        "//sw/top_darjeeling/sw/dif:sram_ctrl",
        "//sw/top_darjeeling/sw/dif:uart",
        "//sw/top_darjeeling/sw/test/utils:alert_handler_testutils",
    ],
)
