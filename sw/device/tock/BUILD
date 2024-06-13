# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "lowrisc_defs",
    srcs = [
        "//hw/ip/adc_ctrl/data:adc_ctrl_rust_regs",
        "//hw/ip/aes/data:aes_rust_regs",
        "//hw/ip/aon_timer/data:aon_timer_rust_regs",
        "//hw/ip/csrng/data:csrng_rust_regs",
        "//hw/ip/edn/data:edn_rust_regs",
        "//hw/ip/entropy_src/data:entropy_src_rust_regs",
        "//hw/ip/gpio/data:gpio_rust_regs",
        "//hw/ip/hmac/data:hmac_rust_regs",
        "//hw/ip/i2c/data:i2c_rust_regs",
        "//hw/ip/keymgr/data:keymgr_rust_regs",
        "//hw/ip/kmac/data:kmac_rust_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_rust_regs",
        "//hw/ip/otbn/data:otbn_rust_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_rust_regs",
        "//hw/ip/pattgen/data:pattgen_rust_regs",
        "//hw/ip/pinmux/data:pinmux_rust_regs",
        "//hw/ip/pwm/data:pwm_rust_regs",
        "//hw/ip/rom_ctrl/data:rom_ctrl_rust_regs",
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_rust_regs",
        "//hw/ip/rv_timer/data:rv_timer_rust_regs",
        "//hw/ip/spi_device/data:spi_device_rust_regs",
        "//hw/ip/spi_host/data:spi_host_rust_regs",
        "//hw/ip/sram_ctrl/data:sram_ctrl_rust_regs",
        "//hw/ip/sysrst_ctrl/data:sysrst_ctrl_rust_regs",
        "//hw/ip/uart/data:uart_rust_regs",
        "//hw/ip/usbdev/data:usbdev_rust_regs",
    ],
    output_group = "tock",
)

filegroup(
    name = "earlgrey_defs",
    srcs = [
        "//hw/top_earlgrey:alert_handler_rust_regs",
        "//hw/top_earlgrey:rv_plic_rust_regs",
        "//hw/top_earlgrey/ip/ast/data:ast_rust_regs",
        "//hw/top_earlgrey/ip/pinmux/data/autogen:pinmux_rust_regs",
        "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_rust_regs",
        "//hw/top_earlgrey/ip_autogen/clkmgr:clkmgr_rust_regs",
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_rust_regs",
        "//hw/top_earlgrey/ip_autogen/pwrmgr:pwrmgr_rust_regs",
        "//hw/top_earlgrey/ip_autogen/rstmgr:rstmgr_rust_regs",
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
