// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/

package top_darjeeling_pkg;
  /**
   * Peripheral base address for uart0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART0_BASE_ADDR = 32'h30010000;

  /**
   * Peripheral size in bytes for uart0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for gpio in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_GPIO_BASE_ADDR = 32'h30000000;

  /**
   * Peripheral size in bytes for gpio in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_GPIO_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for spi_device in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_DEVICE_BASE_ADDR = 32'h30310000;

  /**
   * Peripheral size in bytes for spi_device in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for i2c0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C0_BASE_ADDR = 32'h30080000;

  /**
   * Peripheral size in bytes for i2c0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rv_timer in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_TIMER_BASE_ADDR = 32'h30100000;

  /**
   * Peripheral size in bytes for rv_timer in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR = 32'h30130000;

  /**
   * Peripheral size in bytes for core device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for prim device on otp_macro in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_MACRO_PRIM_BASE_ADDR = 32'h30140000;

  /**
   * Peripheral size in bytes for prim device on otp_macro in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_MACRO_PRIM_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for regs device on lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR = 32'h30150000;

  /**
   * Peripheral size in bytes for regs device on lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_REGS_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for alert_handler in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR = 32'h30160000;

  /**
   * Peripheral size in bytes for alert_handler in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ALERT_HANDLER_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for spi_host0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST0_BASE_ADDR = 32'h30300000;

  /**
   * Peripheral size in bytes for spi_host0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for pwrmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWRMGR_AON_BASE_ADDR = 32'h30400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RSTMGR_AON_BASE_ADDR = 32'h30410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CLKMGR_AON_BASE_ADDR = 32'h30420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CLKMGR_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for pinmux_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PINMUX_AON_BASE_ADDR = 32'h30460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PINMUX_AON_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for aon_timer_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR = 32'h30470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AON_TIMER_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AST_BASE_ADDR = 32'h30480000;

  /**
   * Peripheral size in bytes for ast in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for core device on soc_proxy in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR = 32'h22030000;

  /**
   * Peripheral size in bytes for core device on soc_proxy in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_PROXY_CORE_SIZE_BYTES = 32'h10;

  /**
   * Peripheral base address for ctn device on soc_proxy in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for ctn device on soc_proxy in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_PROXY_CTN_SIZE_BYTES = 32'h40000000;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'h30500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ram device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR = 32'h30600000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for regs device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_REGS_BASE_ADDR = 32'h21200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_REGS_SIZE_BYTES = 32'h10;

  /**
   * Peripheral base address for mem device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_MEM_BASE_ADDR = 32'h40000;

  /**
   * Peripheral size in bytes for mem device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_plic in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_PLIC_BASE_ADDR = 32'h28000000;

  /**
   * Peripheral size in bytes for rv_plic in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AES_BASE_ADDR = 32'h21100000;

  /**
   * Peripheral size in bytes for aes in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for hmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_HMAC_BASE_ADDR = 32'h21110000;

  /**
   * Peripheral size in bytes for hmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_HMAC_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for kmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KMAC_BASE_ADDR = 32'h21120000;

  /**
   * Peripheral size in bytes for kmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otbn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTBN_BASE_ADDR = 32'h21130000;

  /**
   * Peripheral size in bytes for otbn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for keymgr_dpe in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR = 32'h21140000;

  /**
   * Peripheral size in bytes for keymgr_dpe in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KEYMGR_DPE_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for csrng in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CSRNG_BASE_ADDR = 32'h21150000;

  /**
   * Peripheral size in bytes for csrng in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CSRNG_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for entropy_src in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR = 32'h21160000;

  /**
   * Peripheral size in bytes for entropy_src in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ENTROPY_SRC_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for edn0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN0_BASE_ADDR = 32'h21170000;

  /**
   * Peripheral size in bytes for edn0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for edn1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN1_BASE_ADDR = 32'h21180000;

  /**
   * Peripheral size in bytes for edn1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h211C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for regs device on sram_ctrl_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR = 32'h211D0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ram device on sram_ctrl_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR = 32'h11000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for regs device on rom_ctrl0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR = 32'h211E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL0_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL0_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL0_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for regs device on rom_ctrl1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR = 32'h211E1000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL1_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL1_ROM_BASE_ADDR = 32'h20000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL1_ROM_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for dma in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_DMA_BASE_ADDR = 32'h22010000;

  /**
   * Peripheral size in bytes for dma in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_DMA_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on mbx0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX0_CORE_BASE_ADDR = 32'h22000000;

  /**
   * Peripheral size in bytes for core device on mbx0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX0_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX1_CORE_BASE_ADDR = 32'h22000100;

  /**
   * Peripheral size in bytes for core device on mbx1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX1_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX2_CORE_BASE_ADDR = 32'h22000200;

  /**
   * Peripheral size in bytes for core device on mbx2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX2_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX3_CORE_BASE_ADDR = 32'h22000300;

  /**
   * Peripheral size in bytes for core device on mbx3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX3_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx4 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX4_CORE_BASE_ADDR = 32'h22000400;

  /**
   * Peripheral size in bytes for core device on mbx4 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX4_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx5 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX5_CORE_BASE_ADDR = 32'h22000500;

  /**
   * Peripheral size in bytes for core device on mbx5 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX5_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx6 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX6_CORE_BASE_ADDR = 32'h22000600;

  /**
   * Peripheral size in bytes for core device on mbx6 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX6_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx_jtag in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR = 32'h22000800;

  /**
   * Peripheral size in bytes for core device on mbx_jtag in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_JTAG_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx_pcie0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR = 32'h22040000;

  /**
   * Peripheral size in bytes for core device on mbx_pcie0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE0_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on mbx_pcie1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR = 32'h22040100;

  /**
   * Peripheral size in bytes for core device on mbx_pcie1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE1_CORE_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for core device on soc_dbg_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_DBG_CTRL_CORE_BASE_ADDR = 32'h30170000;

  /**
   * Peripheral size in bytes for core device on soc_dbg_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SOC_DBG_CTRL_CORE_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h211F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h800;

  /**
   * Memory base address for ctn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CTN_BASE_ADDR = 32'h40000000;

  /**
   * Memory size for ctn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CTN_SIZE_BYTES = 32'h40000000;

  /**
  * Memory base address for ram_ctn in top darjeeling.
  */
  parameter int unsigned TOP_DARJEELING_RAM_CTN_BASE_ADDR = 32'h41000000;

  /**
  * Memory size for ram_ctn in top darjeeling.
  */
  parameter int unsigned TOP_DARJEELING_RAM_CTN_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_RET_AON_BASE_ADDR = 32'h30600000;

  /**
   * Memory size for ram_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_RET_AON_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for ram_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MAIN_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for ram_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MBOX_BASE_ADDR = 32'h11000000;

  /**
   * Memory size for ram_mbox in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MBOX_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for rom0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM0_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM0_SIZE_BYTES = 32'h8000;

  /**
   * Memory base address for rom1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM1_BASE_ADDR = 32'h20000;

  /**
   * Memory size for rom1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM1_SIZE_BYTES = 32'h10000;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopDarjeelingAlertPeripheralUart0 = 0,
    TopDarjeelingAlertPeripheralGpio = 1,
    TopDarjeelingAlertPeripheralSpiDevice = 2,
    TopDarjeelingAlertPeripheralI2c0 = 3,
    TopDarjeelingAlertPeripheralRvTimer = 4,
    TopDarjeelingAlertPeripheralOtpCtrl = 5,
    TopDarjeelingAlertPeripheralLcCtrl = 6,
    TopDarjeelingAlertPeripheralSpiHost0 = 7,
    TopDarjeelingAlertPeripheralPwrmgrAon = 8,
    TopDarjeelingAlertPeripheralRstmgrAon = 9,
    TopDarjeelingAlertPeripheralClkmgrAon = 10,
    TopDarjeelingAlertPeripheralPinmuxAon = 11,
    TopDarjeelingAlertPeripheralAonTimerAon = 12,
    TopDarjeelingAlertPeripheralSocProxy = 13,
    TopDarjeelingAlertPeripheralSramCtrlRetAon = 14,
    TopDarjeelingAlertPeripheralRvDm = 15,
    TopDarjeelingAlertPeripheralRvPlic = 16,
    TopDarjeelingAlertPeripheralAes = 17,
    TopDarjeelingAlertPeripheralHmac = 18,
    TopDarjeelingAlertPeripheralKmac = 19,
    TopDarjeelingAlertPeripheralOtbn = 20,
    TopDarjeelingAlertPeripheralKeymgrDpe = 21,
    TopDarjeelingAlertPeripheralCsrng = 22,
    TopDarjeelingAlertPeripheralEntropySrc = 23,
    TopDarjeelingAlertPeripheralEdn0 = 24,
    TopDarjeelingAlertPeripheralEdn1 = 25,
    TopDarjeelingAlertPeripheralSramCtrlMain = 26,
    TopDarjeelingAlertPeripheralSramCtrlMbox = 27,
    TopDarjeelingAlertPeripheralRomCtrl0 = 28,
    TopDarjeelingAlertPeripheralRomCtrl1 = 29,
    TopDarjeelingAlertPeripheralDma = 30,
    TopDarjeelingAlertPeripheralMbx0 = 31,
    TopDarjeelingAlertPeripheralMbx1 = 32,
    TopDarjeelingAlertPeripheralMbx2 = 33,
    TopDarjeelingAlertPeripheralMbx3 = 34,
    TopDarjeelingAlertPeripheralMbx4 = 35,
    TopDarjeelingAlertPeripheralMbx5 = 36,
    TopDarjeelingAlertPeripheralMbx6 = 37,
    TopDarjeelingAlertPeripheralMbxJtag = 38,
    TopDarjeelingAlertPeripheralMbxPcie0 = 39,
    TopDarjeelingAlertPeripheralMbxPcie1 = 40,
    TopDarjeelingAlertPeripheralSocDbgCtrl = 41,
    TopDarjeelingAlertPeripheralRaclCtrl = 42,
    TopDarjeelingAlertPeripheralAcRangeCheck = 43,
    TopDarjeelingAlertPeripheralRvCoreIbex = 44,
    TopDarjeelingAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopDarjeelingAlertIdUart0FatalFault = 0,
    TopDarjeelingAlertIdGpioFatalFault = 1,
    TopDarjeelingAlertIdSpiDeviceFatalFault = 2,
    TopDarjeelingAlertIdI2c0FatalFault = 3,
    TopDarjeelingAlertIdRvTimerFatalFault = 4,
    TopDarjeelingAlertIdOtpCtrlFatalMacroError = 5,
    TopDarjeelingAlertIdOtpCtrlFatalCheckError = 6,
    TopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 7,
    TopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 8,
    TopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 9,
    TopDarjeelingAlertIdLcCtrlFatalProgError = 10,
    TopDarjeelingAlertIdLcCtrlFatalStateError = 11,
    TopDarjeelingAlertIdLcCtrlFatalBusIntegError = 12,
    TopDarjeelingAlertIdSpiHost0FatalFault = 13,
    TopDarjeelingAlertIdPwrmgrAonFatalFault = 14,
    TopDarjeelingAlertIdRstmgrAonFatalFault = 15,
    TopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 16,
    TopDarjeelingAlertIdClkmgrAonRecovFault = 17,
    TopDarjeelingAlertIdClkmgrAonFatalFault = 18,
    TopDarjeelingAlertIdPinmuxAonFatalFault = 19,
    TopDarjeelingAlertIdAonTimerAonFatalFault = 20,
    TopDarjeelingAlertIdSocProxyFatalAlertIntg = 21,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal0 = 22,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal1 = 23,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal2 = 24,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal3 = 25,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal4 = 26,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal5 = 27,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal6 = 28,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal7 = 29,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal8 = 30,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal9 = 31,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal10 = 32,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal11 = 33,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal12 = 34,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal13 = 35,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal14 = 36,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal15 = 37,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal16 = 38,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal17 = 39,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal18 = 40,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal19 = 41,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal20 = 42,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal21 = 43,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal22 = 44,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal23 = 45,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal0 = 46,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal1 = 47,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal2 = 48,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal3 = 49,
    TopDarjeelingAlertIdSramCtrlRetAonFatalError = 50,
    TopDarjeelingAlertIdRvDmFatalFault = 51,
    TopDarjeelingAlertIdRvPlicFatalFault = 52,
    TopDarjeelingAlertIdAesRecovCtrlUpdateErr = 53,
    TopDarjeelingAlertIdAesFatalFault = 54,
    TopDarjeelingAlertIdHmacFatalFault = 55,
    TopDarjeelingAlertIdKmacRecovOperationErr = 56,
    TopDarjeelingAlertIdKmacFatalFaultErr = 57,
    TopDarjeelingAlertIdOtbnFatal = 58,
    TopDarjeelingAlertIdOtbnRecov = 59,
    TopDarjeelingAlertIdKeymgrDpeRecovOperationErr = 60,
    TopDarjeelingAlertIdKeymgrDpeFatalFaultErr = 61,
    TopDarjeelingAlertIdCsrngRecovAlert = 62,
    TopDarjeelingAlertIdCsrngFatalAlert = 63,
    TopDarjeelingAlertIdEntropySrcRecovAlert = 64,
    TopDarjeelingAlertIdEntropySrcFatalAlert = 65,
    TopDarjeelingAlertIdEdn0RecovAlert = 66,
    TopDarjeelingAlertIdEdn0FatalAlert = 67,
    TopDarjeelingAlertIdEdn1RecovAlert = 68,
    TopDarjeelingAlertIdEdn1FatalAlert = 69,
    TopDarjeelingAlertIdSramCtrlMainFatalError = 70,
    TopDarjeelingAlertIdSramCtrlMboxFatalError = 71,
    TopDarjeelingAlertIdRomCtrl0Fatal = 72,
    TopDarjeelingAlertIdRomCtrl1Fatal = 73,
    TopDarjeelingAlertIdDmaFatalFault = 74,
    TopDarjeelingAlertIdMbx0FatalFault = 75,
    TopDarjeelingAlertIdMbx0RecovFault = 76,
    TopDarjeelingAlertIdMbx1FatalFault = 77,
    TopDarjeelingAlertIdMbx1RecovFault = 78,
    TopDarjeelingAlertIdMbx2FatalFault = 79,
    TopDarjeelingAlertIdMbx2RecovFault = 80,
    TopDarjeelingAlertIdMbx3FatalFault = 81,
    TopDarjeelingAlertIdMbx3RecovFault = 82,
    TopDarjeelingAlertIdMbx4FatalFault = 83,
    TopDarjeelingAlertIdMbx4RecovFault = 84,
    TopDarjeelingAlertIdMbx5FatalFault = 85,
    TopDarjeelingAlertIdMbx5RecovFault = 86,
    TopDarjeelingAlertIdMbx6FatalFault = 87,
    TopDarjeelingAlertIdMbx6RecovFault = 88,
    TopDarjeelingAlertIdMbxJtagFatalFault = 89,
    TopDarjeelingAlertIdMbxJtagRecovFault = 90,
    TopDarjeelingAlertIdMbxPcie0FatalFault = 91,
    TopDarjeelingAlertIdMbxPcie0RecovFault = 92,
    TopDarjeelingAlertIdMbxPcie1FatalFault = 93,
    TopDarjeelingAlertIdMbxPcie1RecovFault = 94,
    TopDarjeelingAlertIdSocDbgCtrlFatalFault = 95,
    TopDarjeelingAlertIdSocDbgCtrlRecovCtrlUpdateErr = 96,
    TopDarjeelingAlertIdRaclCtrlFatalFault = 97,
    TopDarjeelingAlertIdRaclCtrlRecovCtrlUpdateErr = 98,
    TopDarjeelingAlertIdAcRangeCheckRecovCtrlUpdateErr = 99,
    TopDarjeelingAlertIdAcRangeCheckFatalFault = 100,
    TopDarjeelingAlertIdRvCoreIbexFatalSwErr = 101,
    TopDarjeelingAlertIdRvCoreIbexRecovSwErr = 102,
    TopDarjeelingAlertIdRvCoreIbexFatalHwErr = 103,
    TopDarjeelingAlertIdRvCoreIbexRecovHwErr = 104,
    TopDarjeelingAlertIdCount
  } alert_id_e;

  // Enumeration of interrupts
  typedef enum int unsigned {
    TopDarjeelingPlicIrqIdNone = 0,
    TopDarjeelingPlicIrqIdUart0TxWatermark = 1,
    TopDarjeelingPlicIrqIdUart0RxWatermark = 2,
    TopDarjeelingPlicIrqIdUart0TxDone = 3,
    TopDarjeelingPlicIrqIdUart0RxOverflow = 4,
    TopDarjeelingPlicIrqIdUart0RxFrameErr = 5,
    TopDarjeelingPlicIrqIdUart0RxBreakErr = 6,
    TopDarjeelingPlicIrqIdUart0RxTimeout = 7,
    TopDarjeelingPlicIrqIdUart0RxParityErr = 8,
    TopDarjeelingPlicIrqIdUart0TxEmpty = 9,
    TopDarjeelingPlicIrqIdGpioGpio0 = 10,
    TopDarjeelingPlicIrqIdGpioGpio1 = 11,
    TopDarjeelingPlicIrqIdGpioGpio2 = 12,
    TopDarjeelingPlicIrqIdGpioGpio3 = 13,
    TopDarjeelingPlicIrqIdGpioGpio4 = 14,
    TopDarjeelingPlicIrqIdGpioGpio5 = 15,
    TopDarjeelingPlicIrqIdGpioGpio6 = 16,
    TopDarjeelingPlicIrqIdGpioGpio7 = 17,
    TopDarjeelingPlicIrqIdGpioGpio8 = 18,
    TopDarjeelingPlicIrqIdGpioGpio9 = 19,
    TopDarjeelingPlicIrqIdGpioGpio10 = 20,
    TopDarjeelingPlicIrqIdGpioGpio11 = 21,
    TopDarjeelingPlicIrqIdGpioGpio12 = 22,
    TopDarjeelingPlicIrqIdGpioGpio13 = 23,
    TopDarjeelingPlicIrqIdGpioGpio14 = 24,
    TopDarjeelingPlicIrqIdGpioGpio15 = 25,
    TopDarjeelingPlicIrqIdGpioGpio16 = 26,
    TopDarjeelingPlicIrqIdGpioGpio17 = 27,
    TopDarjeelingPlicIrqIdGpioGpio18 = 28,
    TopDarjeelingPlicIrqIdGpioGpio19 = 29,
    TopDarjeelingPlicIrqIdGpioGpio20 = 30,
    TopDarjeelingPlicIrqIdGpioGpio21 = 31,
    TopDarjeelingPlicIrqIdGpioGpio22 = 32,
    TopDarjeelingPlicIrqIdGpioGpio23 = 33,
    TopDarjeelingPlicIrqIdGpioGpio24 = 34,
    TopDarjeelingPlicIrqIdGpioGpio25 = 35,
    TopDarjeelingPlicIrqIdGpioGpio26 = 36,
    TopDarjeelingPlicIrqIdGpioGpio27 = 37,
    TopDarjeelingPlicIrqIdGpioGpio28 = 38,
    TopDarjeelingPlicIrqIdGpioGpio29 = 39,
    TopDarjeelingPlicIrqIdGpioGpio30 = 40,
    TopDarjeelingPlicIrqIdGpioGpio31 = 41,
    TopDarjeelingPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 42,
    TopDarjeelingPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 43,
    TopDarjeelingPlicIrqIdSpiDeviceUploadPayloadOverflow = 44,
    TopDarjeelingPlicIrqIdSpiDeviceReadbufWatermark = 45,
    TopDarjeelingPlicIrqIdSpiDeviceReadbufFlip = 46,
    TopDarjeelingPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 47,
    TopDarjeelingPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 48,
    TopDarjeelingPlicIrqIdSpiDeviceTpmRdfifoDrop = 49,
    TopDarjeelingPlicIrqIdI2c0FmtThreshold = 50,
    TopDarjeelingPlicIrqIdI2c0RxThreshold = 51,
    TopDarjeelingPlicIrqIdI2c0AcqThreshold = 52,
    TopDarjeelingPlicIrqIdI2c0RxOverflow = 53,
    TopDarjeelingPlicIrqIdI2c0ControllerHalt = 54,
    TopDarjeelingPlicIrqIdI2c0SclInterference = 55,
    TopDarjeelingPlicIrqIdI2c0SdaInterference = 56,
    TopDarjeelingPlicIrqIdI2c0StretchTimeout = 57,
    TopDarjeelingPlicIrqIdI2c0SdaUnstable = 58,
    TopDarjeelingPlicIrqIdI2c0CmdComplete = 59,
    TopDarjeelingPlicIrqIdI2c0TxStretch = 60,
    TopDarjeelingPlicIrqIdI2c0TxThreshold = 61,
    TopDarjeelingPlicIrqIdI2c0AcqStretch = 62,
    TopDarjeelingPlicIrqIdI2c0UnexpStop = 63,
    TopDarjeelingPlicIrqIdI2c0HostTimeout = 64,
    TopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 65,
    TopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone = 66,
    TopDarjeelingPlicIrqIdOtpCtrlOtpError = 67,
    TopDarjeelingPlicIrqIdAlertHandlerClassa = 68,
    TopDarjeelingPlicIrqIdAlertHandlerClassb = 69,
    TopDarjeelingPlicIrqIdAlertHandlerClassc = 70,
    TopDarjeelingPlicIrqIdAlertHandlerClassd = 71,
    TopDarjeelingPlicIrqIdSpiHost0Error = 72,
    TopDarjeelingPlicIrqIdSpiHost0SpiEvent = 73,
    TopDarjeelingPlicIrqIdPwrmgrAonWakeup = 74,
    TopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired = 75,
    TopDarjeelingPlicIrqIdAonTimerAonWdogTimerBark = 76,
    TopDarjeelingPlicIrqIdSocProxyExternal0 = 77,
    TopDarjeelingPlicIrqIdSocProxyExternal1 = 78,
    TopDarjeelingPlicIrqIdSocProxyExternal2 = 79,
    TopDarjeelingPlicIrqIdSocProxyExternal3 = 80,
    TopDarjeelingPlicIrqIdSocProxyExternal4 = 81,
    TopDarjeelingPlicIrqIdSocProxyExternal5 = 82,
    TopDarjeelingPlicIrqIdSocProxyExternal6 = 83,
    TopDarjeelingPlicIrqIdSocProxyExternal7 = 84,
    TopDarjeelingPlicIrqIdSocProxyExternal8 = 85,
    TopDarjeelingPlicIrqIdSocProxyExternal9 = 86,
    TopDarjeelingPlicIrqIdSocProxyExternal10 = 87,
    TopDarjeelingPlicIrqIdSocProxyExternal11 = 88,
    TopDarjeelingPlicIrqIdSocProxyExternal12 = 89,
    TopDarjeelingPlicIrqIdSocProxyExternal13 = 90,
    TopDarjeelingPlicIrqIdSocProxyExternal14 = 91,
    TopDarjeelingPlicIrqIdSocProxyExternal15 = 92,
    TopDarjeelingPlicIrqIdSocProxyExternal16 = 93,
    TopDarjeelingPlicIrqIdSocProxyExternal17 = 94,
    TopDarjeelingPlicIrqIdSocProxyExternal18 = 95,
    TopDarjeelingPlicIrqIdSocProxyExternal19 = 96,
    TopDarjeelingPlicIrqIdSocProxyExternal20 = 97,
    TopDarjeelingPlicIrqIdSocProxyExternal21 = 98,
    TopDarjeelingPlicIrqIdSocProxyExternal22 = 99,
    TopDarjeelingPlicIrqIdSocProxyExternal23 = 100,
    TopDarjeelingPlicIrqIdSocProxyExternal24 = 101,
    TopDarjeelingPlicIrqIdSocProxyExternal25 = 102,
    TopDarjeelingPlicIrqIdSocProxyExternal26 = 103,
    TopDarjeelingPlicIrqIdSocProxyExternal27 = 104,
    TopDarjeelingPlicIrqIdSocProxyExternal28 = 105,
    TopDarjeelingPlicIrqIdSocProxyExternal29 = 106,
    TopDarjeelingPlicIrqIdSocProxyExternal30 = 107,
    TopDarjeelingPlicIrqIdSocProxyExternal31 = 108,
    TopDarjeelingPlicIrqIdHmacHmacDone = 109,
    TopDarjeelingPlicIrqIdHmacFifoEmpty = 110,
    TopDarjeelingPlicIrqIdHmacHmacErr = 111,
    TopDarjeelingPlicIrqIdKmacKmacDone = 112,
    TopDarjeelingPlicIrqIdKmacFifoEmpty = 113,
    TopDarjeelingPlicIrqIdKmacKmacErr = 114,
    TopDarjeelingPlicIrqIdOtbnDone = 115,
    TopDarjeelingPlicIrqIdKeymgrDpeOpDone = 116,
    TopDarjeelingPlicIrqIdCsrngCsCmdReqDone = 117,
    TopDarjeelingPlicIrqIdCsrngCsEntropyReq = 118,
    TopDarjeelingPlicIrqIdCsrngCsHwInstExc = 119,
    TopDarjeelingPlicIrqIdCsrngCsFatalErr = 120,
    TopDarjeelingPlicIrqIdEntropySrcEsEntropyValid = 121,
    TopDarjeelingPlicIrqIdEntropySrcEsHealthTestFailed = 122,
    TopDarjeelingPlicIrqIdEntropySrcEsObserveFifoReady = 123,
    TopDarjeelingPlicIrqIdEntropySrcEsFatalErr = 124,
    TopDarjeelingPlicIrqIdEdn0EdnCmdReqDone = 125,
    TopDarjeelingPlicIrqIdEdn0EdnFatalErr = 126,
    TopDarjeelingPlicIrqIdEdn1EdnCmdReqDone = 127,
    TopDarjeelingPlicIrqIdEdn1EdnFatalErr = 128,
    TopDarjeelingPlicIrqIdDmaDmaDone = 129,
    TopDarjeelingPlicIrqIdDmaDmaChunkDone = 130,
    TopDarjeelingPlicIrqIdDmaDmaError = 131,
    TopDarjeelingPlicIrqIdMbx0MbxReady = 132,
    TopDarjeelingPlicIrqIdMbx0MbxAbort = 133,
    TopDarjeelingPlicIrqIdMbx0MbxError = 134,
    TopDarjeelingPlicIrqIdMbx1MbxReady = 135,
    TopDarjeelingPlicIrqIdMbx1MbxAbort = 136,
    TopDarjeelingPlicIrqIdMbx1MbxError = 137,
    TopDarjeelingPlicIrqIdMbx2MbxReady = 138,
    TopDarjeelingPlicIrqIdMbx2MbxAbort = 139,
    TopDarjeelingPlicIrqIdMbx2MbxError = 140,
    TopDarjeelingPlicIrqIdMbx3MbxReady = 141,
    TopDarjeelingPlicIrqIdMbx3MbxAbort = 142,
    TopDarjeelingPlicIrqIdMbx3MbxError = 143,
    TopDarjeelingPlicIrqIdMbx4MbxReady = 144,
    TopDarjeelingPlicIrqIdMbx4MbxAbort = 145,
    TopDarjeelingPlicIrqIdMbx4MbxError = 146,
    TopDarjeelingPlicIrqIdMbx5MbxReady = 147,
    TopDarjeelingPlicIrqIdMbx5MbxAbort = 148,
    TopDarjeelingPlicIrqIdMbx5MbxError = 149,
    TopDarjeelingPlicIrqIdMbx6MbxReady = 150,
    TopDarjeelingPlicIrqIdMbx6MbxAbort = 151,
    TopDarjeelingPlicIrqIdMbx6MbxError = 152,
    TopDarjeelingPlicIrqIdMbxJtagMbxReady = 153,
    TopDarjeelingPlicIrqIdMbxJtagMbxAbort = 154,
    TopDarjeelingPlicIrqIdMbxJtagMbxError = 155,
    TopDarjeelingPlicIrqIdMbxPcie0MbxReady = 156,
    TopDarjeelingPlicIrqIdMbxPcie0MbxAbort = 157,
    TopDarjeelingPlicIrqIdMbxPcie0MbxError = 158,
    TopDarjeelingPlicIrqIdMbxPcie1MbxReady = 159,
    TopDarjeelingPlicIrqIdMbxPcie1MbxAbort = 160,
    TopDarjeelingPlicIrqIdMbxPcie1MbxError = 161,
    TopDarjeelingPlicIrqIdRaclCtrlRaclError = 162,
    TopDarjeelingPlicIrqIdAcRangeCheckDenyCntReached = 163,
    TopDarjeelingPlicIrqIdCount
  } interrupt_rv_plic_id_e;


  // Enumeration of IO power domains.
  // Only used in ASIC target.
  typedef enum logic [0:0] {
    IoBankVio = 0,
    IoBankCount = 1
  } pwr_dom_e;

  // Enumeration for MIO signals on the top-level.
  typedef enum int unsigned {
    MioInSocProxySocGpi12 = 0,
    MioInSocProxySocGpi13 = 1,
    MioInSocProxySocGpi14 = 2,
    MioInSocProxySocGpi15 = 3,
    MioInCount = 4
  } mio_in_e;

  typedef enum {
    MioOutSocProxySocGpo12 = 0,
    MioOutSocProxySocGpo13 = 1,
    MioOutSocProxySocGpo14 = 2,
    MioOutSocProxySocGpo15 = 3,
    MioOutOtpMacroTest0 = 4,
    MioOutCount = 5
  } mio_out_e;

  // Enumeration for DIO signals, used on both the top and chip-levels.
  typedef enum int unsigned {
    DioSpiHost0Sd0 = 0,
    DioSpiHost0Sd1 = 1,
    DioSpiHost0Sd2 = 2,
    DioSpiHost0Sd3 = 3,
    DioSpiDeviceSd0 = 4,
    DioSpiDeviceSd1 = 5,
    DioSpiDeviceSd2 = 6,
    DioSpiDeviceSd3 = 7,
    DioI2c0Scl = 8,
    DioI2c0Sda = 9,
    DioGpioGpio0 = 10,
    DioGpioGpio1 = 11,
    DioGpioGpio2 = 12,
    DioGpioGpio3 = 13,
    DioGpioGpio4 = 14,
    DioGpioGpio5 = 15,
    DioGpioGpio6 = 16,
    DioGpioGpio7 = 17,
    DioGpioGpio8 = 18,
    DioGpioGpio9 = 19,
    DioGpioGpio10 = 20,
    DioGpioGpio11 = 21,
    DioGpioGpio12 = 22,
    DioGpioGpio13 = 23,
    DioGpioGpio14 = 24,
    DioGpioGpio15 = 25,
    DioGpioGpio16 = 26,
    DioGpioGpio17 = 27,
    DioGpioGpio18 = 28,
    DioGpioGpio19 = 29,
    DioGpioGpio20 = 30,
    DioGpioGpio21 = 31,
    DioGpioGpio22 = 32,
    DioGpioGpio23 = 33,
    DioGpioGpio24 = 34,
    DioGpioGpio25 = 35,
    DioGpioGpio26 = 36,
    DioGpioGpio27 = 37,
    DioGpioGpio28 = 38,
    DioGpioGpio29 = 39,
    DioGpioGpio30 = 40,
    DioGpioGpio31 = 41,
    DioSpiDeviceSck = 42,
    DioSpiDeviceCsb = 43,
    DioSpiDeviceTpmCsb = 44,
    DioUart0Rx = 45,
    DioSocProxySocGpi0 = 46,
    DioSocProxySocGpi1 = 47,
    DioSocProxySocGpi2 = 48,
    DioSocProxySocGpi3 = 49,
    DioSocProxySocGpi4 = 50,
    DioSocProxySocGpi5 = 51,
    DioSocProxySocGpi6 = 52,
    DioSocProxySocGpi7 = 53,
    DioSocProxySocGpi8 = 54,
    DioSocProxySocGpi9 = 55,
    DioSocProxySocGpi10 = 56,
    DioSocProxySocGpi11 = 57,
    DioSpiHost0Sck = 58,
    DioSpiHost0Csb = 59,
    DioUart0Tx = 60,
    DioSocProxySocGpo0 = 61,
    DioSocProxySocGpo1 = 62,
    DioSocProxySocGpo2 = 63,
    DioSocProxySocGpo3 = 64,
    DioSocProxySocGpo4 = 65,
    DioSocProxySocGpo5 = 66,
    DioSocProxySocGpo6 = 67,
    DioSocProxySocGpo7 = 68,
    DioSocProxySocGpo8 = 69,
    DioSocProxySocGpo9 = 70,
    DioSocProxySocGpo10 = 71,
    DioSocProxySocGpo11 = 72,
    DioCount = 73
  } dio_e;

  // Enumeration for the types of pads.
  typedef enum {
    MioPad,
    DioPad
  } pad_type_e;

  // Raw MIO/DIO input array indices on chip-level.
  // TODO: Does not account for target specific stubbed/added pads.
  // Need to make a target-specific package for those.
  typedef enum int unsigned {
    MioPadMio0 = 0,
    MioPadMio1 = 1,
    MioPadMio2 = 2,
    MioPadMio3 = 3,
    MioPadMio4 = 4,
    MioPadMio5 = 5,
    MioPadMio6 = 6,
    MioPadMio7 = 7,
    MioPadMio8 = 8,
    MioPadMio9 = 9,
    MioPadMio10 = 10,
    MioPadMio11 = 11,
    MioPadCount
  } mio_pad_e;

  typedef enum int unsigned {
    DioPadPorN = 0,
    DioPadJtagTck = 1,
    DioPadJtagTms = 2,
    DioPadJtagTdi = 3,
    DioPadJtagTdo = 4,
    DioPadJtagTrstN = 5,
    DioPadOtpExtVolt = 6,
    DioPadSpiHostD0 = 7,
    DioPadSpiHostD1 = 8,
    DioPadSpiHostD2 = 9,
    DioPadSpiHostD3 = 10,
    DioPadSpiHostClk = 11,
    DioPadSpiHostCsL = 12,
    DioPadSpiDevD0 = 13,
    DioPadSpiDevD1 = 14,
    DioPadSpiDevD2 = 15,
    DioPadSpiDevD3 = 16,
    DioPadSpiDevClk = 17,
    DioPadSpiDevCsL = 18,
    DioPadSpiDevTpmCsL = 19,
    DioPadUartRx = 20,
    DioPadUartTx = 21,
    DioPadI2cScl = 22,
    DioPadI2cSda = 23,
    DioPadGpio0 = 24,
    DioPadGpio1 = 25,
    DioPadGpio2 = 26,
    DioPadGpio3 = 27,
    DioPadGpio4 = 28,
    DioPadGpio5 = 29,
    DioPadGpio6 = 30,
    DioPadGpio7 = 31,
    DioPadGpio8 = 32,
    DioPadGpio9 = 33,
    DioPadGpio10 = 34,
    DioPadGpio11 = 35,
    DioPadGpio12 = 36,
    DioPadGpio13 = 37,
    DioPadGpio14 = 38,
    DioPadGpio15 = 39,
    DioPadGpio16 = 40,
    DioPadGpio17 = 41,
    DioPadGpio18 = 42,
    DioPadGpio19 = 43,
    DioPadGpio20 = 44,
    DioPadGpio21 = 45,
    DioPadGpio22 = 46,
    DioPadGpio23 = 47,
    DioPadGpio24 = 48,
    DioPadGpio25 = 49,
    DioPadGpio26 = 50,
    DioPadGpio27 = 51,
    DioPadGpio28 = 52,
    DioPadGpio29 = 53,
    DioPadGpio30 = 54,
    DioPadGpio31 = 55,
    DioPadSocGpi0 = 56,
    DioPadSocGpi1 = 57,
    DioPadSocGpi2 = 58,
    DioPadSocGpi3 = 59,
    DioPadSocGpi4 = 60,
    DioPadSocGpi5 = 61,
    DioPadSocGpi6 = 62,
    DioPadSocGpi7 = 63,
    DioPadSocGpi8 = 64,
    DioPadSocGpi9 = 65,
    DioPadSocGpi10 = 66,
    DioPadSocGpi11 = 67,
    DioPadSocGpo0 = 68,
    DioPadSocGpo1 = 69,
    DioPadSocGpo2 = 70,
    DioPadSocGpo3 = 71,
    DioPadSocGpo4 = 72,
    DioPadSocGpo5 = 73,
    DioPadSocGpo6 = 74,
    DioPadSocGpo7 = 75,
    DioPadSocGpo8 = 76,
    DioPadSocGpo9 = 77,
    DioPadSocGpo10 = 78,
    DioPadSocGpo11 = 79,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralAes,
    PeripheralAlertHandler,
    PeripheralAonTimerAon,
    PeripheralAst,
    PeripheralClkmgrAon,
    PeripheralCsrng,
    PeripheralDma,
    PeripheralEdn0,
    PeripheralEdn1,
    PeripheralEntropySrc,
    PeripheralGpio,
    PeripheralHmac,
    PeripheralI2c0,
    PeripheralKeymgrDpe,
    PeripheralKmac,
    PeripheralLcCtrl,
    PeripheralMbx0,
    PeripheralMbx1,
    PeripheralMbx2,
    PeripheralMbx3,
    PeripheralMbx4,
    PeripheralMbx5,
    PeripheralMbx6,
    PeripheralMbxJtag,
    PeripheralMbxPcie0,
    PeripheralMbxPcie1,
    PeripheralOtbn,
    PeripheralOtpCtrl,
    PeripheralOtpMacro,
    PeripheralPinmuxAon,
    PeripheralPwrmgrAon,
    PeripheralRomCtrl0,
    PeripheralRomCtrl1,
    PeripheralRstmgrAon,
    PeripheralRvCoreIbex,
    PeripheralRvDm,
    PeripheralRvPlic,
    PeripheralRvTimer,
    PeripheralSocDbgCtrl,
    PeripheralSocProxy,
    PeripheralSpiDevice,
    PeripheralSpiHost0,
    PeripheralSramCtrlMain,
    PeripheralSramCtrlMbox,
    PeripheralSramCtrlRetAon,
    PeripheralUart0,
    PeripheralCount
  } peripheral_e;

  // MMIO Region
  //
  parameter int unsigned TOP_DARJEELING_MMIO_BASE_ADDR = 32'h21100000;
  parameter int unsigned TOP_DARJEELING_MMIO_SIZE_BYTES = 32'hF501000;

  // TODO: Enumeration for PLIC Interrupt source peripheral.

// MACROs for AST analog simulation support
`ifdef ANALOGSIM
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
`endif

endpackage
