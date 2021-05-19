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
  import kmac_app_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [63:0]  RND_CNST_SCR_NONCE = 64'h0123456789ABCDEF;
  parameter bit [127:0] RND_CNST_SCR_KEY   = 128'hFEDCBA9876543210FEDCBA9876543210;

  parameter string LIST_OF_ALERTS[] = {"fatal"};
  parameter uint   NUM_ALERTS = 1;

  // The top bytes in memory hold the digest
  parameter uint MAX_CHECK_ADDR = rom_ctrl_reg_pkg::ROM_CTRL_ROM_SIZE - (kmac_pkg::AppDigestW / 8);
  // The data for each line in rom up to the digest is padded out to the kmac message width
  parameter uint KMAC_DATA_SIZE = MAX_CHECK_ADDR / (TL_DW / 8) * (kmac_pkg::MsgWidth / 8);
  // The rom width is rounded up to 40 for scrambling symmetry
  parameter uint ROM_MEM_W = 40;

  // types
  typedef virtual mem_bkdr_if #(.MEM_ECC(prim_secded_pkg::Secded_39_32)) mem_bkdr_vif;
  typedef virtual rom_ctrl_if rom_ctrl_vif;

  // functions

  // package sources
  `include "rom_ctrl_env_cfg.sv"
  `include "rom_ctrl_env_cov.sv"
  `include "rom_ctrl_virtual_sequencer.sv"
  `include "rom_ctrl_scoreboard.sv"
  `include "rom_ctrl_env.sv"
  `include "rom_ctrl_vseq_list.sv"

endpackage
