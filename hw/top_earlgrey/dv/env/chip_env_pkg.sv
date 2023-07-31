// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package chip_env_pkg;

  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;

  import ast_pkg::AstRegsNum, ast_pkg::AstLastRegOffset;
  import bus_params_pkg::*;
  import chip_ral_pkg::*;
  import chip_common_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import digestpp_dpi_pkg::*;
  import aes_model_dpi_pkg::*;
  import dv_base_reg_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import flash_ctrl_pkg::*;
  import jtag_pkg::*;
  import jtag_agent_pkg::*;
  import jtag_riscv_agent_pkg::*;
  import jtag_dmi_agent_pkg::*;
  import jtag_rv_debugger_pkg::*;
  import prim_secded_pkg::*;
  import rv_dm_regs_ral_pkg::*;
  import rv_dm_mem_ral_pkg::*;
  import rv_dm_reg_pkg::NrHarts;
  import rv_dm_reg_pkg::NumAlerts;
  import kmac_pkg::*;
  import aes_pkg::*;
  import lc_ctrl_state_pkg::*;
  import lc_ctrl_dv_utils_pkg::*;
  import mem_bkdr_util_pkg::*;
  import otp_ctrl_pkg::*;
  import spi_agent_pkg::*;
  import sram_ctrl_pkg::*;
  import str_utils_pkg::*;
  import sw_test_status_pkg::*;
  import tl_agent_pkg::*;
  import uart_agent_pkg::*;
  import xbar_env_pkg::*;
  import top_earlgrey_pkg::*;
  import top_earlgrey_rnd_cnst_pkg::*;
  import pwm_monitor_pkg::*;
  import pwm_reg_pkg::NOutputs;
  import tl_main_pkg::ADDR_SPACE_RV_CORE_IBEX__CFG;
  import rv_core_ibex_reg_pkg::RV_CORE_IBEX_DV_SIM_WINDOW_OFFSET;
  import i2c_agent_pkg::*;
  import pattgen_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "chip_hier_macros.svh"

  // LC token paramters
  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit  = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;

  // ROM digest parameters
  localparam uint RomDigestDw = 256;
  localparam uint RomMaxCheckAddr = rom_ctrl_reg_pkg::ROM_CTRL_ROM_SIZE - (RomDigestDw / 8);

  typedef virtual sw_logger_if         sw_logger_vif;
  typedef virtual sw_test_status_if    sw_test_status_vif;
  typedef virtual ast_supply_if        ast_supply_vif;
  typedef virtual ast_ext_clk_if       ast_ext_clk_vif;
  typedef virtual usb20_if             usb20_vif;

  // Types of memories in the chip.
  //
  // RAM instances have support for up to 16 tiles. Actual number of tiles in use in the design is a
  // runtime setting in chip_env_cfg.
  typedef enum {
    FlashBank0Data,
    FlashBank1Data,
    FlashBank0Info,
    FlashBank1Info,
    ICacheWay0Tag,
    ICacheWay1Tag,
    ICacheWay0Data,
    ICacheWay1Data,
    UsbdevBuf,
    OtbnDmem[16],
    OtbnImem,
    Otp,
    RamMain[16],
    RamRet[16],
    Rom
  } chip_mem_e;

  // On OpenTitan, we deal with 4 types of SW - ROM, the main test, the OTBN test and the OTP image.
  // This basically puts these SW types into 'slots' that the external regression tool can set.
  typedef enum {
    SwTypeRom       = 0, // Ibex SW - first stage boot ROM.
    SwTypeTestSlotA = 1, // Ibex SW - test SW in (flash) slot A.
    SwTypeTestSlotB = 2, // Ibex SW - test SW in (flash) slot B.
    SwTypeOtbn      = 3, // Otbn SW
    SwTypeOtp       = 4, // Customized OTP image
    SwTypeDebug     = 5  // Debug SW - injected into SRAM.
  } sw_type_e;

  // Our dvsim.py configuration always generates five base OTP images (in various lifecycle states)
  // to allow tests configurations to choose from. Additionally, we support specifying a custom OTP
  // image, via the `sw_images` plusarg, that is built by the SW build system.
  typedef enum {
    OtpTypeLcStRaw,           // Base OTP image in Raw lifecycle state.
    OtpTypeLcStDev,           // Base OTP image in Dev lifecycle state.
    OtpTypeLcStProd,          // Base OTP image in Prod lifecycle state.
    OtpTypeLcStRma,           // Base OTP image in RMA lifecycle state.
    OtpTypeLcStTestUnlocked0, // Base OTP image in TestUnlocked0 lifecycle state.
    OtpTypeLcStTestUnlocked1, // Base OTP image in TestUnlocked1 lifecycle state.
    OtpTypeLcStTestUnlocked2, // Base OTP image in TestUnlocked2 lifecycle state.
    OtpTypeLcStTestLocked0, // Base OTP image in TestUnlocked0 lifecycle state.
    OtpTypeLcStTestLocked1, // Base OTP image in TestUnlocked0 lifecycle state.
    OtpTypeCustom             // Custom OTP image specified via `sw_images` plusarg.
  } otp_type_e;

  // Two status for LC JTAG to identify if LC state transition is successful.
  typedef enum int {
    LcInitialized,
    LcReady,
    LcExtClockSwitched,
    LcTransitionSuccessful,
    LcTransitionCntError,
    LcTransitionError,
    LcTokenError,
    LcFlashRmaError,
    LcOtpError,
    LcStateError,
    LcBusIntegError,
    LcOtpPartitionError
  } lc_ctrl_status_e;

  typedef enum bit[1:0] {
    SysrstCtrlPadKey0 = 0,
    SysrstCtrlPadKey1 = 1,
    SysrstCtrlPadKey2 = 2
  } sysrst_ctrl_pad_key_idx_e;

  // Typical SPI flash opcodes.
  typedef enum bit [7:0] {
    SpiFlashReadJedec    = 8'h9F,
    SpiFlashReadSfdp     = 8'h5A,
    SpiFlashReadNormal   = 8'h03,
    SpiFlashReadFast     = 8'h0B,
    SpiFlashReadDual     = 8'h3B,
    SpiFlashReadQuad     = 8'h6B,
    SpiFlashReadSts1     = 8'h05,
    SpiFlashReadSts2     = 8'h35,
    SpiFlashReadSts3     = 8'h15,
    SpiFlashWriteDisable = 8'h04,
    SpiFlashWriteEnable  = 8'h06,
    SpiFlashWriteSts1    = 8'h01,
    SpiFlashWriteSts2    = 8'h31,
    SpiFlashWriteSts3    = 8'h11,
    SpiFlashChipErase    = 8'hC7,
    SpiFlashSectorErase  = 8'h20,
    SpiFlashPageProgram  = 8'h02,
    SpiFlashEn4B         = 8'hB7,
    SpiFlashEx4B         = 8'hE9
  } spi_flash_cmd_e;

  // package sources
  `include "chip_env_cfg.sv"
  `include "chip_env_cov.sv"
  `include "chip_virtual_sequencer.sv"
  `include "chip_scoreboard.sv"
  `include "chip_env.sv"
  `include "chip_vseq_list.sv"

endpackage
