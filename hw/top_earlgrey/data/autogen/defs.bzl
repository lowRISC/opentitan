# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
#                -o hw/top_earlgrey/

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

EARLGREY_IPS = [
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
]

EARLGREY_ALERTS = [
    "uart0_fatal_fault",
    "uart1_fatal_fault",
    "uart2_fatal_fault",
    "uart3_fatal_fault",
    "gpio_fatal_fault",
    "spi_device_fatal_fault",
    "i2c0_fatal_fault",
    "i2c1_fatal_fault",
    "i2c2_fatal_fault",
    "pattgen_fatal_fault",
    "rv_timer_fatal_fault",
    "otp_ctrl_fatal_macro_error",
    "otp_ctrl_fatal_check_error",
    "otp_ctrl_fatal_bus_integ_error",
    "otp_ctrl_fatal_prim_otp_alert",
    "otp_ctrl_recov_prim_otp_alert",
    "lc_ctrl_fatal_prog_error",
    "lc_ctrl_fatal_state_error",
    "lc_ctrl_fatal_bus_integ_error",
    "spi_host0_fatal_fault",
    "spi_host1_fatal_fault",
    "usbdev_fatal_fault",
    "pwrmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_cnsty_fault",
    "clkmgr_aon_recov_fault",
    "clkmgr_aon_fatal_fault",
    "sysrst_ctrl_aon_fatal_fault",
    "adc_ctrl_aon_fatal_fault",
    "pwm_aon_fatal_fault",
    "pinmux_aon_fatal_fault",
    "aon_timer_aon_fatal_fault",
    "sensor_ctrl_aon_recov_alert",
    "sensor_ctrl_aon_fatal_alert",
    "sram_ctrl_ret_aon_fatal_error",
    "flash_ctrl_recov_err",
    "flash_ctrl_fatal_std_err",
    "flash_ctrl_fatal_err",
    "flash_ctrl_fatal_prim_flash_alert",
    "flash_ctrl_recov_prim_flash_alert",
    "rv_dm_fatal_fault",
    "rv_plic_fatal_fault",
    "aes_recov_ctrl_update_err",
    "aes_fatal_fault",
    "hmac_fatal_fault",
    "kmac_recov_operation_err",
    "kmac_fatal_fault_err",
    "otbn_fatal",
    "otbn_recov",
    "keymgr_recov_operation_err",
    "keymgr_fatal_fault_err",
    "csrng_recov_alert",
    "csrng_fatal_alert",
    "entropy_src_recov_alert",
    "entropy_src_fatal_alert",
    "edn0_recov_alert",
    "edn0_fatal_alert",
    "edn1_recov_alert",
    "edn1_fatal_alert",
    "sram_ctrl_main_fatal_error",
    "rom_ctrl_fatal",
    "rv_core_ibex_fatal_sw_err",
    "rv_core_ibex_recov_sw_err",
    "rv_core_ibex_fatal_hw_err",
    "rv_core_ibex_recov_hw_err",
]
