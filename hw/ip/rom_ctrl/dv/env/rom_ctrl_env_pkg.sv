// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rom_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;

  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import cip_base_pkg::*;
  import tl_agent_pkg::*;

  import rom_ctrl_bkdr_util_pkg::*;
  import kmac_app_agent_pkg::*;

  import top_pkg::*;
  import rom_ctrl_regs_ral_pkg::*;
  import rom_ctrl_prim_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [63:0]  RND_CNST_SCR_NONCE = 64'h0123456789ABCDEF;
  parameter bit [127:0] RND_CNST_SCR_KEY   = 128'hFEDCBA9876543210FEDCBA9876543210;

  parameter uint   NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"fatal"};

  // The exact ROM size in bytes.
  // Will be set to 32 KiB for ROM0 and 64 KiB ROM1.
  // Can be a non-power-of-2 size but must be a multiple of 16 KiB for due to the
  // scrambling.
  `ifndef ROM_SIZE_BYTES
    `define ROM_SIZE_BYTES 2**15
  `endif

  // The top bytes in memory hold the digest
  // KMAC's max digest size is larger than what is required, so declare the size here.
  parameter uint DIGEST_SIZE    = 256;

  // These are the sizes for ROM for the block-level testbench. The environment shouldn't consume
  // them without checking that we are in a block-level context.
  parameter uint ROM_SIZE_BYTES = `ROM_SIZE_BYTES;
  parameter uint ROM_SIZE_WORDS = ROM_SIZE_BYTES / (TL_DW / 8);

  // The rom width in bits
  parameter uint ROM_MEM_W = 39;

  // types
  typedef virtual rom_ctrl_if rom_ctrl_vif;
  typedef class rom_ctrl_scoreboard;

  `include "rom_ctrl_addr_force_item.svh"
  `include "rom_ctrl_addr_force_driver.svh"
  typedef uvm_sequencer #(rom_ctrl_addr_force_item) rom_ctrl_addr_force_sequencer_t;
  `include "seq_lib/rom_ctrl_skip_middle_seq.svh"

  `include "rom_ctrl_kmac_rsp_force_item.svh"
  `include "rom_ctrl_kmac_rsp_force_driver.svh"
  typedef uvm_sequencer #(rom_ctrl_kmac_rsp_force_item) rom_ctrl_kmac_rsp_force_sequencer_t;
  `include "seq_lib/rom_ctrl_override_digest_seq.svh"

  `include "seq_lib/rom_ctrl_skip_middle_with_digest_vseq.svh"

  `include "rom_ctrl_env_cfg.sv"
  `include "rom_ctrl_env_cov.sv"
  `include "rom_ctrl_virtual_sequencer.sv"
  `include "rom_ctrl_scoreboard.sv"
  `include "rom_ctrl_env.sv"

endpackage
