// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sends one OTP macro request and waits for its response.
//
// Set the request fields before starting the sequence. The item's constraints check that the
// request is legal. After start() returns, rsp_item holds the complete transaction, including
// rdata and err.
class otp_macro_base_seq extends dv_base_seq #(
  .REQ         (otp_macro_item),
  .CFG_T       (otp_macro_agent_cfg),
  .SEQUENCER_T (otp_macro_sequencer)
);
  `uvm_object_utils(otp_macro_base_seq)

  cmd_e            cmd;
  otp_macro_size_t size;
  otp_macro_addr_t addr;
  otp_macro_data_t wdata;

  // The completed transaction, available once the sequence has finished.
  otp_macro_item rsp_item;

  extern function new(string name = "");
  extern task body();
endclass : otp_macro_base_seq

function otp_macro_base_seq::new(string name = "");
  super.new(name);
endfunction : new

task otp_macro_base_seq::body();
  rsp_item = otp_macro_item::type_id::create("rsp_item");
  start_item(rsp_item);
  `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp_item,
                                 cmd   == local::cmd;
                                 size  == local::size;
                                 addr  == local::addr;
                                 wdata == local::wdata;)
  finish_item(rsp_item);
endtask : body
