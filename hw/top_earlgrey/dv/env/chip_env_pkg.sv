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
  import dv_base_reg_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import flash_ctrl_pkg::*;
  import jtag_pkg::*;
  import jtag_agent_pkg::*;
  import jtag_riscv_agent_pkg::*;
  import jtag_dmi_agent_pkg::*;
  import rv_dm_regs_ral_pkg::*;
  import rv_dm_debug_mem_ral_pkg::*;
  import rv_dm_reg_pkg::NrHarts;
  import rv_dm_reg_pkg::NumAlerts;
  import kmac_pkg::*;
  import lc_ctrl_state_pkg::*;
  import mem_bkdr_util_pkg::*;
  import otp_ctrl_pkg::*;
  import spi_agent_pkg::*;
  import sram_ctrl_pkg::*;
  import str_utils_pkg::*;
  import sw_test_status_pkg::*;
  import tl_agent_pkg::*;
  import uart_agent_pkg::*;
  import spi_agent_pkg::*;
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

  typedef virtual sw_logger_if         sw_logger_vif;
  typedef virtual sw_test_status_if    sw_test_status_vif;
  typedef virtual ast_supply_if        ast_supply_vif;
  typedef virtual ast_ext_clk_if       ast_ext_clk_vif;

  // Types of memories in the chip.
  //
  // RAM instances have support for up to 16 tiles. Actual number of tiles in use in the design is a
  // runtime setting in chip_env_cfg.
  typedef enum {
    FlashBank0Data,
    FlashBank1Data,
    FlashBank0Info,
    FlashBank1Info,
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
    SwTypeRom,  // Ibex SW - first stage boot ROM.
    SwTypeTest, // Ibex SW - actual test SW.
    SwTypeOtbn  // Otbn SW.
  } sw_type_e;

  // Two status for LC JTAG to identify if LC state transition is successful.
  typedef enum int {
    LcReady,
    LcTransitionSuccessful,
    LcTransitionCntError,
    LcTransitionError,
    LcTokenError,
    LcFlashRmaError,
    LcOtpError
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
    SpiFlashChipErase    = 8'hC7,
    SpiFlashSectorErase  = 8'h20,
    SpiFlashPageProgram  = 8'h02,
    SpiFlashEn4B         = 8'hB7,
    SpiFlashEx4B         = 8'hE9
  } spi_flash_cmd_e;

  // Extracts the address and size of a const symbol in a SW test (supplied as an ELF file).
  //
  // Used by a testbench to modify the given symbol in an executable (elf) generated for an embedded
  // CPU within the DUT. This function only returns the extracted address and size of the symbol
  // using the readelf utility. Readelf comes with binutils, a package typically available on user
  // / corp machines. If not available, the assumption is, it can be relatively easily installed.
  // The actual job of writing the new value into the symbol is handled externally (often via a
  // backdoor mechanism to write the memory).
  // Return 1 on success and 0 on failure.
  function automatic bit sw_symbol_get_addr_size(input string elf_file,
                                                 input string symbol,
                                                 input bit does_not_exist_ok,
                                                 output longint unsigned addr,
                                                 output longint unsigned size);

    string msg_id = "sw_symbol_get_addr_size";
    `DV_CHECK_STRNE_FATAL(elf_file, "", "Input arg \"elf_file\" cannot be an empty string", msg_id)
    `DV_CHECK_STRNE_FATAL(symbol,   "", "Input arg \"symbol\" cannot be an empty string", msg_id)

    begin
      int ret;
      string line;
      int out_file_d = 0;
      string out_file = $sformatf("%0s.dat", symbol);
      string cmd = $sformatf(
          // use `--wide` to avoid truncating the output, in case of long symbol name
          "/usr/bin/readelf -s --wide %0s | grep %0s | awk \'{print $2\" \"$3}\' > %0s",
          elf_file, symbol, out_file);

      // TODO #3838: shell pipes are bad 'mkay?
      ret = $system(cmd);
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Command \"%0s\" failed with exit code %0d", cmd, ret),
                         msg_id)

      out_file_d = $fopen(out_file, "r");
      `DV_CHECK_FATAL(out_file_d, $sformatf("Failed to open \"%0s\"", out_file), msg_id)

      ret = $fgets(line, out_file_d);

      // If the symbol did not exist in the elf (empty file), and we are ok with that, then return.
      if (!ret && does_not_exist_ok) return 0;

      `DV_CHECK_FATAL(ret, $sformatf("Failed to read line from \"%0s\"", out_file), msg_id)

      // The first line should have the addr in hex followed by its size as integer.
      ret = $sscanf(line, "%h %d", addr, size);
      `DV_CHECK_EQ_FATAL(ret, 2, $sformatf("Failed to extract {addr size} from line \"%0s\"", line),
                         msg_id)

      // Attempt to read the next line should be met with EOF.
      void'($fgets(line, out_file_d));
      ret = $feof(out_file_d);
      `DV_CHECK_FATAL(ret, $sformatf("EOF expected to be reached for \"%0s\"", out_file), msg_id)
      $fclose(out_file_d);

      ret = $system($sformatf("rm -rf %0s", out_file));
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Failed to delete \"%0s\"", out_file), msg_id)
      return 1;
    end
  endfunction

  // package sources
  `include "chip_env_cfg.sv"
  `include "chip_env_cov.sv"
  `include "chip_virtual_sequencer.sv"
  `include "chip_scoreboard.sv"
  `include "chip_env.sv"
  `include "chip_vseq_list.sv"

endpackage
