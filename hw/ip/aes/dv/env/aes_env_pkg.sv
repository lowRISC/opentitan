// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import aes_reg_pkg::*;
  import aes_ral_pkg::*;
  import aes_pkg::*;


  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"ctrl_err_update", "ctrl_err_storage"};
  parameter uint NUM_ALERTS = 2;

  typedef enum int { AES_CFG=0, AES_DATA=1, AES_ERR_INJ=2 } aes_item_type_e;

  // functions

  // package sources
 `include "aes_env_cfg.sv"
 `include "aes_seq_item.sv"
 `include "aes_message_item.sv"
 `include "aes_env_cov.sv"
 `include "aes_virtual_sequencer.sv"
 `include "aes_scoreboard.sv"
 `include "aes_env.sv"
 `include "aes_vseq_list.sv"

endpackage
