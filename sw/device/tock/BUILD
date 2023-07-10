# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "lowrisc_defs",
    srcs = [
        "//hw/ip/adc_ctrl/data:adc_ctrl_regs",
        "//hw/ip/aes/data:aes_regs",
        "//hw/ip/aon_timer/data:aon_timer_regs",
        "//hw/ip/clkmgr/data:clkmgr_regs",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/gpio/data:gpio_regs",
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/ip/i2c/data:i2c_regs",
        "//hw/ip/keymgr/data:keymgr_regs",
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/ip/pattgen/data:pattgen_regs",
        "//hw/ip/pinmux/data:pinmux_regs",
        "//hw/ip/pwm/data:pwm_regs",
        "//hw/ip/rom_ctrl/data:rom_ctrl_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_regs",
        "//hw/ip/rv_timer/data:rv_timer_regs",
        "//hw/ip/spi_device/data:spi_device_regs",
        "//hw/ip/spi_host/data:spi_host_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_regs",
        "//hw/ip/uart/data:uart_regs",
        "//hw/ip/usbdev/data:usbdev_regs",
    ],
    output_group = "tock",
)

filegroup(
    name = "earlgrey_defs",
    srcs = [
        "//hw/top_earlgrey:alert_handler_regs",
        "//hw/top_earlgrey:rv_plic_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_regs",
        "//hw/top_earlgrey/ip/clkmgr/data/autogen:clkmgr_regs",
        "//hw/top_earlgrey/ip/flash_ctrl/data/autogen:flash_ctrl_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_regs",
        "//hw/top_earlgrey/ip/pwrmgr/data/autogen:pwrmgr_regs",
        "//hw/top_earlgrey/ip/rstmgr/data/autogen:rstmgr_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
    ],
    output_group = "tock",
)

filegroup(
    name = "earlgrey_top_defs",
    srcs = [
        "//hw/top_earlgrey/sw/autogen/chip:mod.rs",
        "//hw/top_earlgrey/sw/autogen/chip:top_earlgrey.rs",
    ],
)

pkg_tar(
    name = "tock_lowrisc_registers",
    srcs = [":lowrisc_defs"],
    mode = "0644",
    package_dir = "chips/lowrisc/src/registers",
)

pkg_tar(
    name = "tock_earlgrey_registers",
    srcs = [":earlgrey_defs"],
    mode = "0644",
    package_dir = "chips/earlgrey/src/registers",
)

pkg_tar(
    name = "tock_earlgrey_top",
    srcs = [":earlgrey_top_defs"],
    mode = "0644",
    package_dir = "chips/earlgrey/src/top",
)
