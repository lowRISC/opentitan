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
  import push_pull_agent_pkg::*;
  import aes_reg_pkg::*;
  import aes_ral_pkg::*;
  import aes_pkg::*;
  import key_sideload_agent_pkg::*;


  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef virtual key_sideload_if   sideload_vif;
  // parameters
  parameter string LIST_OF_ALERTS[] = {"recov_ctrl_update_err", "fatal_fault"};
  parameter uint NUM_ALERTS = 2;
  parameter uint NUM_EDN = 1;

  typedef enum int { AES_CFG=0, AES_DATA=1, AES_ERR_INJ=2 } aes_item_type_e;
  typedef enum int { Flip_bits = 0, Pull_reset = 1, Lc_escalate = 2 } flip_rst_lc_esc_e;

  typedef struct packed {
    bit          dataout;
    bit          key_iv_data_in;
  } clear_t;

  typedef struct packed {
    bit          lc_esc;
    bit          reset;
    bit          mal_inject;
    bit          cfg;
  } error_types_t;

  typedef struct packed {
    bit          key_len;
    bit          mode;
    bit          rsd_rate;
  } cfg_error_type_t;


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
