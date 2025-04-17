# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rtl_files",
    srcs = glob(
        ["**"],
        exclude = [
            "*/dv/**",
            "*/doc/**",
            "*/README.md",
        ],
    ) + [
        "//hw/ip/adc_ctrl:rtl_files",
        "//hw/ip/aes:rtl_files",
        "//hw/ip/aon_timer:rtl_files",
        "//hw/ip/csrng:rtl_files",
        "//hw/ip/edn:rtl_files",
        "//hw/ip/entropy_src:rtl_files",
        "//hw/ip/hmac:rtl_files",
        "//hw/ip/i2c:rtl_files",
        "//hw/ip/keymgr:rtl_files",
        "//hw/ip/kmac:rtl_files",
        "//hw/ip/lc_ctrl:rtl_files",
        "//hw/ip/otbn:rtl_files",
        "//hw/ip/otp_ctrl:rtl_files",
        "//hw/ip/otp_macro:rtl_files",
        "//hw/ip/pattgen:rtl_files",
        "//hw/ip/prim:rtl_files",
        "//hw/ip/prim_generic:rtl_files",
        "//hw/ip/prim_xilinx:rtl_files",
        "//hw/ip/prim_xilinx_ultrascale:rtl_files",
        "//hw/ip/rom_ctrl:rtl_files",
        "//hw/ip/rv_dm:rtl_files",
        "//hw/ip/rv_timer:rtl_files",
        "//hw/ip/spi_device:rtl_files",
        "//hw/ip/spi_host:rtl_files",
        "//hw/ip/sram_ctrl:rtl_files",
        "//hw/ip/sysrst_ctrl:rtl_files",
        "//hw/ip/tlul:rtl_files",
        "//hw/ip/trial1:rtl_files",
        "//hw/ip/uart:rtl_files",
        "//hw/ip/usbdev:rtl_files",
    ],
)

filegroup(
    name = "verilator_files",
    srcs = [
        ":rtl_files",
        "//hw/ip/prim:verilator_files",
    ],
)
