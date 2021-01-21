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
  parameter string LIST_OF_ALERTS[] = {"recov_ctrl_update_err", "fatal_fault"};
  parameter uint NUM_ALERTS = 2;

  typedef enum int { AES_CFG=0, AES_DATA=1, AES_ERR_INJ=2 } aes_item_type_e;

  typedef struct packed {
    bit          data_out;
    bit          data_in;
    bit          iv;
    bit          key;
  } clear_t;

  typedef struct packed {
    bit          reset;
    bit          mal_inject;
    bit          cfg;
  } error_types_t;

  typedef struct packed {
    bit          key_len;
    bit          mode;
  } cfg_error_type_t;

  typedef struct packed {
    logic [31:7] unused;
    logic        alert_fatal_fault;
    logic        alert_recov_ctrl_update_err;
    logic        input_ready;
    logic        output_valid;
    logic        output_lost;
    logic        stall;
    logic        idle;
  } status_t;


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
