# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
# -o hw/top_englishbreakfast

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/ip/aes:defs.bzl", "AES")
load("//hw/ip/aon_timer:defs.bzl", "AON_TIMER")
load("//hw/top_englishbreakfast/ip/ast:defs.bzl", "AST")
load("//hw/top_englishbreakfast/ip_autogen/clkmgr:defs.bzl", "CLKMGR")
load("//hw/top_englishbreakfast/ip_autogen/flash_ctrl:defs.bzl", "FLASH_CTRL")
load("//hw/ip/gpio:defs.bzl", "GPIO")
load("//hw/top_englishbreakfast/ip_autogen/pinmux:defs.bzl", "PINMUX")
load("//hw/top_englishbreakfast/ip_autogen/pwrmgr:defs.bzl", "PWRMGR")
load("//hw/ip/rom_ctrl:defs.bzl", "ROM_CTRL")
load("//hw/top_englishbreakfast/ip_autogen/rstmgr:defs.bzl", "RSTMGR")
load("//hw/ip/rv_core_ibex:defs.bzl", "RV_CORE_IBEX")
load("//hw/top_englishbreakfast/ip_autogen/rv_plic:defs.bzl", "RV_PLIC")
load("//hw/ip/rv_timer:defs.bzl", "RV_TIMER")
load("//hw/ip/spi_device:defs.bzl", "SPI_DEVICE")
load("//hw/ip/spi_host:defs.bzl", "SPI_HOST")
load("//hw/ip/sram_ctrl:defs.bzl", "SRAM_CTRL")
load("//hw/ip/uart:defs.bzl", "UART")
load("//hw/ip/usbdev:defs.bzl", "USBDEV")

ENGLISHBREAKFAST = opentitan_top(
    name = "englishbreakfast",
    hjson = "//hw/top_englishbreakfast/data/autogen:top_englishbreakfast.gen.hjson",
    top_lib = "//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast",
    top_ld = "//hw/top_englishbreakfast/sw/autogen:top_englishbreakfast_memory",
    ips = [
        AES,
        AON_TIMER,
        AST,
        CLKMGR,
        FLASH_CTRL,
        GPIO,
        PINMUX,
        PWRMGR,
        ROM_CTRL,
        RSTMGR,
        RV_CORE_IBEX,
        RV_PLIC,
        RV_TIMER,
        SPI_DEVICE,
        SPI_HOST,
        SRAM_CTRL,
        UART,
        USBDEV,
    ],
)

ENGLISHBREAKFAST_ALERTS = [
    "uart0_fatal_fault",
    "uart1_fatal_fault",
    "gpio_fatal_fault",
    "spi_device_fatal_fault",
    "spi_host0_fatal_fault",
    "rv_timer_fatal_fault",
    "usbdev_fatal_fault",
    "pwrmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_cnsty_fault",
    "clkmgr_aon_recov_fault",
    "clkmgr_aon_fatal_fault",
    "pinmux_aon_fatal_fault",
    "aon_timer_aon_fatal_fault",
    "flash_ctrl_recov_err",
    "flash_ctrl_fatal_std_err",
    "flash_ctrl_fatal_err",
    "flash_ctrl_fatal_prim_flash_alert",
    "flash_ctrl_recov_prim_flash_alert",
    "rv_plic_fatal_fault",
    "aes_recov_ctrl_update_err",
    "aes_fatal_fault",
    "sram_ctrl_main_fatal_error",
    "rom_ctrl_fatal",
    "rv_core_ibex_fatal_sw_err",
    "rv_core_ibex_recov_sw_err",
    "rv_core_ibex_fatal_hw_err",
    "rv_core_ibex_recov_hw_err",
]
