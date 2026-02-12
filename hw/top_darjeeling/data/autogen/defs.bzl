# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------#
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
# util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
#                -o hw/top_darjeeling/

load("//hw/top_darjeeling/ip_autogen/ac_range_check:defs.bzl", "AC_RANGE_CHECK")
load("//hw/ip/aes:defs.bzl", "AES")
load("//hw/top_darjeeling/ip_autogen/alert_handler:defs.bzl", "ALERT_HANDLER")
load("//hw/ip/aon_timer:defs.bzl", "AON_TIMER")
load("//hw/top_darjeeling/ip/ast:defs.bzl", "AST")
load("//hw/top_darjeeling/ip_autogen/clkmgr:defs.bzl", "CLKMGR")
load("//hw/ip/csrng:defs.bzl", "CSRNG")
load("//hw/ip/dma:defs.bzl", "DMA")
load("//hw/ip/edn:defs.bzl", "EDN")
load("//hw/ip/entropy_src:defs.bzl", "ENTROPY_SRC")
load("//hw/top_darjeeling/ip_autogen/gpio:defs.bzl", "GPIO")
load("//hw/ip/hmac:defs.bzl", "HMAC")
load("//hw/ip/i2c:defs.bzl", "I2C")
load("//hw/ip/keymgr_dpe:defs.bzl", "KEYMGR_DPE")
load("//hw/ip/kmac:defs.bzl", "KMAC")
load("//hw/ip/lc_ctrl:defs.bzl", "LC_CTRL")
load("//hw/ip/mbx:defs.bzl", "MBX")
load("//hw/ip/otbn:defs.bzl", "OTBN")
load("//hw/top_darjeeling/ip_autogen/otp_ctrl:defs.bzl", "OTP_CTRL")
load("//hw/ip/otp_macro:defs.bzl", "OTP_MACRO")
load("//hw/top_darjeeling/ip_autogen/pinmux:defs.bzl", "PINMUX")
load("//hw/top_darjeeling/ip_autogen/pwrmgr:defs.bzl", "PWRMGR")
load("//hw/top_darjeeling/ip_autogen/racl_ctrl:defs.bzl", "RACL_CTRL")
load("//hw/ip/rom_ctrl:defs.bzl", "ROM_CTRL")
load("//hw/top_darjeeling/ip_autogen/rstmgr:defs.bzl", "RSTMGR")
load("//hw/top_darjeeling/ip_autogen/rv_core_ibex:defs.bzl", "RV_CORE_IBEX")
load("//hw/ip/rv_dm:defs.bzl", "RV_DM")
load("//hw/top_darjeeling/ip_autogen/rv_plic:defs.bzl", "RV_PLIC")
load("//hw/ip/rv_timer:defs.bzl", "RV_TIMER")
load("//hw/ip/soc_dbg_ctrl:defs.bzl", "SOC_DBG_CTRL")
load("//hw/top_darjeeling/ip/soc_proxy:defs.bzl", "SOC_PROXY")
load("//hw/ip/spi_device:defs.bzl", "SPI_DEVICE")
load("//hw/ip/spi_host:defs.bzl", "SPI_HOST")
load("//hw/ip/sram_ctrl:defs.bzl", "SRAM_CTRL")
load("//hw/ip/uart:defs.bzl", "UART")

DARJEELING_IPS = [
    AC_RANGE_CHECK,
    AES,
    ALERT_HANDLER,
    AON_TIMER,
    AST,
    CLKMGR,
    CSRNG,
    DMA,
    EDN,
    ENTROPY_SRC,
    GPIO,
    HMAC,
    I2C,
    KEYMGR_DPE,
    KMAC,
    LC_CTRL,
    MBX,
    OTBN,
    OTP_CTRL,
    OTP_MACRO,
    PINMUX,
    PWRMGR,
    RACL_CTRL,
    ROM_CTRL,
    RSTMGR,
    RV_CORE_IBEX,
    RV_DM,
    RV_PLIC,
    RV_TIMER,
    SOC_DBG_CTRL,
    SOC_PROXY,
    SPI_DEVICE,
    SPI_HOST,
    SRAM_CTRL,
    UART,
]

DARJEELING_ALERTS = [
    "uart0_fatal_fault",
    "gpio_fatal_fault",
    "spi_device_fatal_fault",
    "i2c0_fatal_fault",
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
    "pwrmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_cnsty_fault",
    "clkmgr_aon_recov_fault",
    "clkmgr_aon_fatal_fault",
    "pinmux_aon_fatal_fault",
    "aon_timer_aon_fatal_fault",
    "soc_proxy_fatal_alert_intg",
    "sram_ctrl_ret_aon_fatal_error",
    "rv_dm_fatal_fault",
    "rv_plic_fatal_fault",
    "aes_recov_ctrl_update_err",
    "aes_fatal_fault",
    "hmac_fatal_fault",
    "kmac_recov_operation_err",
    "kmac_fatal_fault_err",
    "otbn_fatal",
    "otbn_recov",
    "keymgr_dpe_recov_operation_err",
    "keymgr_dpe_fatal_fault_err",
    "csrng_recov_alert",
    "csrng_fatal_alert",
    "entropy_src_recov_alert",
    "entropy_src_fatal_alert",
    "edn0_recov_alert",
    "edn0_fatal_alert",
    "edn1_recov_alert",
    "edn1_fatal_alert",
    "sram_ctrl_main_fatal_error",
    "sram_ctrl_mbox_fatal_error",
    "rom_ctrl0_fatal",
    "rom_ctrl1_fatal",
    "dma_fatal_fault",
    "mbx0_fatal_fault",
    "mbx0_recov_fault",
    "mbx1_fatal_fault",
    "mbx1_recov_fault",
    "mbx2_fatal_fault",
    "mbx2_recov_fault",
    "mbx3_fatal_fault",
    "mbx3_recov_fault",
    "mbx4_fatal_fault",
    "mbx4_recov_fault",
    "mbx5_fatal_fault",
    "mbx5_recov_fault",
    "mbx6_fatal_fault",
    "mbx6_recov_fault",
    "mbx_jtag_fatal_fault",
    "mbx_jtag_recov_fault",
    "mbx_pcie0_fatal_fault",
    "mbx_pcie0_recov_fault",
    "mbx_pcie1_fatal_fault",
    "mbx_pcie1_recov_fault",
    "soc_dbg_ctrl_fatal_fault",
    "soc_dbg_ctrl_recov_ctrl_update_err",
    "racl_ctrl_fatal_fault",
    "racl_ctrl_recov_ctrl_update_err",
    "ac_range_check_recov_ctrl_update_err",
    "ac_range_check_fatal_fault",
    "rv_core_ibex_fatal_sw_err",
    "rv_core_ibex_recov_sw_err",
    "rv_core_ibex_fatal_hw_err",
    "rv_core_ibex_recov_hw_err",
]
