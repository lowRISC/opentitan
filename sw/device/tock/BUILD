# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "lowrisc_defs",
    srcs = [
        "//hw/top:adc_ctrl_rust_regs",
        "//hw/top:aes_rust_regs",
        "//hw/top:aon_timer_rust_regs",
        "//hw/top:csrng_rust_regs",
        "//hw/top:edn_rust_regs",
        "//hw/top:entropy_src_rust_regs",
        "//hw/top:gpio_rust_regs",
        "//hw/top:hmac_rust_regs",
        "//hw/top:i2c_rust_regs",
        "//hw/top:keymgr_rust_regs",
        "//hw/top:kmac_rust_regs",
        "//hw/top:lc_ctrl_rust_regs",
        "//hw/top:otbn_rust_regs",
        "//hw/top:otp_ctrl_rust_regs",
        "//hw/top:pattgen_rust_regs",
        "//hw/top:pwm_rust_regs",
        "//hw/top:rom_ctrl_rust_regs",
        "//hw/top:rv_core_ibex_rust_regs",
        "//hw/top:rv_timer_rust_regs",
        "//hw/top:spi_device_rust_regs",
        "//hw/top:spi_host_rust_regs",
        "//hw/top:sram_ctrl_rust_regs",
        "//hw/top:sysrst_ctrl_rust_regs",
        "//hw/top:uart_rust_regs",
        "//hw/top:usbdev_rust_regs",
    ],
    output_group = "tock",
)

filegroup(
    name = "earlgrey_defs",
    srcs = [
        "//hw/top:alert_handler_rust_regs",
        "//hw/top:ast_rust_regs",
        "//hw/top:clkmgr_rust_regs",
        "//hw/top:flash_ctrl_rust_regs",
        "//hw/top:otp_ctrl_rust_regs",
        "//hw/top:pinmux_rust_regs",
        "//hw/top:pwrmgr_rust_regs",
        "//hw/top:rstmgr_rust_regs",
        "//hw/top:rv_plic_rust_regs",
        "//hw/top:sensor_ctrl_rust_regs",
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
