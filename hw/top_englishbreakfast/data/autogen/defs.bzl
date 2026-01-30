# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
#                -o hw/top_englishbreakfast/

load("@lowrisc_opentitan//hw/ip/aes:defs.bzl", "AES")
load("@lowrisc_opentitan//hw/ip/aon_timer:defs.bzl", "AON_TIMER")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip/ast:defs.bzl", "AST")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/clkmgr:defs.bzl", "CLKMGR")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/flash_ctrl:defs.bzl", "FLASH_CTRL")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/gpio:defs.bzl", "GPIO")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/pinmux:defs.bzl", "PINMUX")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/pwrmgr:defs.bzl", "PWRMGR")
load("@lowrisc_opentitan//hw/ip/rom_ctrl:defs.bzl", "ROM_CTRL")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/rstmgr:defs.bzl", "RSTMGR")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/rv_core_ibex:defs.bzl", "RV_CORE_IBEX")
load("@lowrisc_opentitan//hw/top_englishbreakfast/ip_autogen/rv_plic:defs.bzl", "RV_PLIC")
load("@lowrisc_opentitan//hw/ip/rv_timer:defs.bzl", "RV_TIMER")
load("@lowrisc_opentitan//hw/ip/spi_device:defs.bzl", "SPI_DEVICE")
load("@lowrisc_opentitan//hw/ip/spi_host:defs.bzl", "SPI_HOST")
load("@lowrisc_opentitan//hw/ip/sram_ctrl:defs.bzl", "SRAM_CTRL")
load("@lowrisc_opentitan//hw/ip/uart:defs.bzl", "UART")
load("@lowrisc_opentitan//hw/ip/usbdev:defs.bzl", "USBDEV")

ENGLISHBREAKFAST_IPS = [
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
]

ENGLISHBREAKFAST_ALERTS = [
]
