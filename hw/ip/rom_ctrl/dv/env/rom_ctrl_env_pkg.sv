// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rom_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rom_ctrl_regs_ral_pkg::*;
  import rom_ctrl_rom_ral_pkg::*;
  import kmac_app_agent_pkg::*;
  import mem_bkdr_util_pkg::*;
  import prim_mubi_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [63:0]  RND_CNST_SCR_NONCE = 64'h0123456789ABCDEF;
  parameter bit [127:0] RND_CNST_SCR_KEY   = 128'hFEDCBA9876543210FEDCBA9876543210;

  parameter string LIST_OF_ALERTS[] = {"fatal"};
  parameter uint   NUM_ALERTS = 1;

  // The top bytes in memory hold the digest
  // KMAC's max digest size is larger than what is required, so declare the size here.
  parameter uint DIGEST_SIZE    = 256;
  parameter uint MAX_CHECK_ADDR = rom_ctrl_reg_pkg::ROM_CTRL_ROM_SIZE - (DIGEST_SIZE / 8);
  // The data for each line in rom up to the digest padded to the next byte boundary
  parameter uint KMAC_DATA_WORD_SIZE = (39 + 7) / 8;
  parameter uint KMAC_DATA_NUM_WORDS = MAX_CHECK_ADDR / (TL_DW / 8);
  parameter uint KMAC_DATA_SIZE = KMAC_DATA_NUM_WORDS * KMAC_DATA_WORD_SIZE;
  // The rom width in bits
  parameter uint ROM_MEM_W = 39;

  // types
  typedef virtual rom_ctrl_if rom_ctrl_vif;
  typedef class rom_ctrl_scoreboard;

  // functions

  // package sources
  `include "rom_ctrl_env_cfg.sv"
  `include "rom_ctrl_env_cov.sv"
  `include "rom_ctrl_virtual_sequencer.sv"
  `include "rom_ctrl_scoreboard.sv"
  `include "rom_ctrl_env.sv"
  `include "rom_ctrl_vseq_list.sv"

endpackage
