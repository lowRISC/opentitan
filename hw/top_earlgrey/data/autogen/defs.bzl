# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
# -o hw/top_earlgrey

load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/ip/adc_ctrl:defs.bzl", "ADC_CTRL")
load("//hw/ip/aes:defs.bzl", "AES")
load("//hw/top_earlgrey/ip_autogen/alert_handler:defs.bzl", "ALERT_HANDLER")
load("//hw/ip/aon_timer:defs.bzl", "AON_TIMER")
load("//hw/top_earlgrey/ip/ast:defs.bzl", "AST")
load("//hw/top_earlgrey/ip_autogen/clkmgr:defs.bzl", "CLKMGR")
load("//hw/ip/csrng:defs.bzl", "CSRNG")
load("//hw/ip/edn:defs.bzl", "EDN")
load("//hw/ip/entropy_src:defs.bzl", "ENTROPY_SRC")
load("//hw/top_earlgrey/ip_autogen/flash_ctrl:defs.bzl", "FLASH_CTRL")
load("//hw/top_earlgrey/ip_autogen/gpio:defs.bzl", "GPIO")
load("//hw/ip/hmac:defs.bzl", "HMAC")
load("//hw/ip/i2c:defs.bzl", "I2C")
load("//hw/ip/keymgr:defs.bzl", "KEYMGR")
load("//hw/ip/kmac:defs.bzl", "KMAC")
load("//hw/ip/lc_ctrl:defs.bzl", "LC_CTRL")
load("//hw/ip/otbn:defs.bzl", "OTBN")
load("//hw/top_earlgrey/ip_autogen/otp_ctrl:defs.bzl", "OTP_CTRL")
load("//hw/ip/otp_macro:defs.bzl", "OTP_MACRO")
load("//hw/ip/pattgen:defs.bzl", "PATTGEN")
load("//hw/top_earlgrey/ip_autogen/pinmux:defs.bzl", "PINMUX")
load("//hw/top_earlgrey/ip_autogen/pwm:defs.bzl", "PWM")
load("//hw/top_earlgrey/ip_autogen/pwrmgr:defs.bzl", "PWRMGR")
load("//hw/ip/rom_ctrl:defs.bzl", "ROM_CTRL")
load("//hw/top_earlgrey/ip_autogen/rstmgr:defs.bzl", "RSTMGR")
load("//hw/top_earlgrey/ip_autogen/rv_core_ibex:defs.bzl", "RV_CORE_IBEX")
load("//hw/ip/rv_dm:defs.bzl", "RV_DM")
load("//hw/top_earlgrey/ip_autogen/rv_plic:defs.bzl", "RV_PLIC")
load("//hw/ip/rv_timer:defs.bzl", "RV_TIMER")
load("//hw/top_earlgrey/ip/sensor_ctrl:defs.bzl", "SENSOR_CTRL")
load("//hw/ip/spi_device:defs.bzl", "SPI_DEVICE")
load("//hw/ip/spi_host:defs.bzl", "SPI_HOST")
load("//hw/ip/sram_ctrl:defs.bzl", "SRAM_CTRL")
load("//hw/ip/sysrst_ctrl:defs.bzl", "SYSRST_CTRL")
load("//hw/ip/uart:defs.bzl", "UART")
load("//hw/ip/usbdev:defs.bzl", "USBDEV")

EARLGREY = opentitan_top(
    name = "earlgrey",
    hjson = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    top_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    top_ld = "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ips = [
        ADC_CTRL,
        AES,
        ALERT_HANDLER,
        AON_TIMER,
        AST,
        CLKMGR,
        CSRNG,
        EDN,
        ENTROPY_SRC,
        FLASH_CTRL,
        GPIO,
        HMAC,
        I2C,
        KEYMGR,
        KMAC,
        LC_CTRL,
        OTBN,
        OTP_CTRL,
        OTP_MACRO,
        PATTGEN,
        PINMUX,
        PWM,
        PWRMGR,
        ROM_CTRL,
        RSTMGR,
        RV_CORE_IBEX,
        RV_DM,
        RV_PLIC,
        RV_TIMER,
        SENSOR_CTRL,
        SPI_DEVICE,
        SPI_HOST,
        SRAM_CTRL,
        SYSRST_CTRL,
        UART,
        USBDEV,
    ],
)
