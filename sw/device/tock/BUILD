# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "lowrisc_defs",
    srcs = [
        "//hw/top/tock:adc_ctrl_regs",
        "//hw/top/tock:aes_regs",
        "//hw/top/tock:aon_timer_regs",
        "//hw/top/tock:csrng_regs",
        "//hw/top/tock:edn_regs",
        "//hw/top/tock:entropy_src_regs",
        "//hw/top/tock:gpio_regs",
        "//hw/top/tock:hmac_regs",
        "//hw/top/tock:i2c_regs",
        "//hw/top/tock:keymgr_regs",
        "//hw/top/tock:kmac_regs",
        "//hw/top/tock:lc_ctrl_regs",
        "//hw/top/tock:otbn_regs",
        "//hw/top/tock:otp_ctrl_regs",
        "//hw/top/tock:pattgen_regs",
        "//hw/top/tock:pwm_regs",
        "//hw/top/tock:rom_ctrl_regs",
        "//hw/top/tock:rv_core_ibex_regs",
        "//hw/top/tock:rv_timer_regs",
        "//hw/top/tock:spi_device_regs",
        "//hw/top/tock:spi_host_regs",
        "//hw/top/tock:sram_ctrl_regs",
        "//hw/top/tock:sysrst_ctrl_regs",
        "//hw/top/tock:uart_regs",
        "//hw/top/tock:usbdev_regs",
    ],
    output_group = "tock",
)

filegroup(
    name = "earlgrey_defs",
    srcs = [
        "//hw/top/tock:alert_handler_regs",
        "//hw/top/tock:ast_regs",
        "//hw/top/tock:clkmgr_regs",
        "//hw/top/tock:flash_ctrl_regs",
        "//hw/top/tock:otp_ctrl_regs",
        "//hw/top/tock:pinmux_regs",
        "//hw/top/tock:pwrmgr_regs",
        "//hw/top/tock:rstmgr_regs",
        "//hw/top/tock:rv_plic_regs",
        "//hw/top/tock:sensor_ctrl_regs",
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
