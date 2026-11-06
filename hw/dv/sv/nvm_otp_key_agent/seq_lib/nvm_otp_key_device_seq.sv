// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Answers every key request seen by the monitor.
//
// The keys are picked once, when the sequence is randomized, and the same key is returned for
// every request of the same kind, including after a reset. That matches a provisioned otp_ctrl,
// whose keys only change if the device is reprovisioned. Only the ack delay changes per request.
class nvm_otp_key_device_seq extends dv_base_seq #(
  .REQ         (nvm_otp_key_item),
  .CFG_T       (nvm_otp_key_agent_cfg),
  .SEQUENCER_T (nvm_otp_key_sequencer)
);
  `uvm_object_utils(nvm_otp_key_device_seq)

  // Key material returned for each kind of request, indexed by nvm_otp_key_kind_e.
  rand nvm_otp_key_t m_key[NumNvmOtpKeyKinds];
  rand nvm_otp_key_t m_rand_key[NumNvmOtpKeyKinds];
  rand bit           m_seed_valid;

  constraint m_seed_valid_c {
    soft m_seed_valid == 1'b1;
  }

  extern function new(string name = "");
  extern task body();
endclass : nvm_otp_key_device_seq

function nvm_otp_key_device_seq::new(string name = "");
  super.new(name);
endfunction : new

task nvm_otp_key_device_seq::body();
  forever begin
    nvm_otp_key_item req_item;
    nvm_otp_key_item rsp_item;

    p_sequencer.req_analysis_fifo.get(req_item);

    rsp_item = nvm_otp_key_item::type_id::create("rsp_item");
    rsp_item.kind = req_item.kind;
    start_item(rsp_item);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp_item,
                                   key        == local::m_key[req_item.kind];
                                   rand_key   == local::m_rand_key[req_item.kind];
                                   seed_valid == local::m_seed_valid;
                                   ack_delay inside {[cfg.ack_delay_min:cfg.ack_delay_max]};)
    finish_item(rsp_item);
  end
endtask : body
