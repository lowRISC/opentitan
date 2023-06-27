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

  typedef enum int {
    AES_CFG     = 0,
    AES_DATA    = 1,
    AES_ERR_INJ = 2
  } aes_item_type_e;

  typedef enum int {
    ShadowRegStorageErr = 0,
    PullReset           = 1,
    LcEscalate          = 2,
    AlertTest           = 3
  } alert_reset_trigger_e;

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

  // used in FI verification seq and if
  localparam int StateWidth = 6;


  // Pick a name for this interface, under which it will be registered with the UVM DB. This is
  // based on IfName but also appends the index under the deepest generate block if necessary. For
  // example, if IfName is "foo" and we're bound into a module that is instantiated with indices 0,
  // 1 and 2 and then this should return "foo_0", "foo_1" and "foo_2", respectively.
  function automatic string pick_if_name(string IfName, string str);
    // find the interface index
    string suffix = "";
    int    closing_bracket = -1;
    int    opening_bracket  = -1;

    // Walk from the back, searching for something of the form "[123]".
    for (int i = str.len() - 1; i >= 0; i--) begin
      if (str[i] == "]") begin
        closing_bracket = i;
        break;
      end
    end
    for (int i = str.len() - 1; i >= 0; i--) begin
      if (str[i] == "[") begin
        opening_bracket = i;
        break;
      end
    end
    if (str[opening_bracket] == "[") begin
      // we do not expect to see "[]"
      if (!(closing_bracket > opening_bracket + 1)) begin
        // we cannot use macro as module is not a part of hierarchy
        // will fail the get_full_name() lookup
        `uvm_fatal($sformatf("%m"), $sformatf("Found unexpected empty bracket"))
      end
      // Put the stuff in the brackets in suffix
      suffix = str.substr(opening_bracket + 1, closing_bracket - 1);
    end

    return $sformatf("%s_%s", IfName, suffix);
  endfunction

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
