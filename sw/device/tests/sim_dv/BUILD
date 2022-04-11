# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

opentitan_functest(
    name = "flash_ctrl_lc_rw_en_test",
    srcs = ["flash_ctrl_lc_rw_en_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "gpio_test",
    srcs = ["gpio_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib:pinmux",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "keymgr_key_derivation",
    srcs = ["keymgr_key_derivation.c"],
    deps = [
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:keymgr",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "lc_ctrl_transition_test",
    srcs = ["lc_ctrl_transition_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "pwrmgr_main_power_glitch_test",
    srcs = ["pwrmgr_main_power_glitch_test.c"],
    deps = [
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
    ],
)

opentitan_functest(
    name = "pwrmgr_usbdev_smoketest",
    srcs = ["pwrmgr_usbdev_smoketest.c"],
    deps = [
        "//sw/device/lib:usb",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
    ],
)

opentitan_functest(
    name = "rom_ctrl_integrity_check_test",
    srcs = ["rom_ctrl_integrity_check_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:rom_ctrl",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "spi_tx_rx_test",
    srcs = ["spi_tx_rx_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/dif:spi_device",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_functest(
    name = "sram_ctrl_execution_test_main",
    srcs = ["sram_ctrl_execution_test_main.c"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/dif:sram_ctrl",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "sram_ctrl_main_scrambled_access_test",
    srcs = ["sram_ctrl_main_scrambled_access_test.c"],
    deps = [
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/base:multibits",
        "//sw/device/lib/base:stdasm",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing:sram_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "sram_ctrl_ret_scrambled_access_test",
    srcs = ["sram_ctrl_ret_scrambled_access_test.c"],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:sram_ctrl_testutils",
    ],
)
