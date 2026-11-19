// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The sequencer used by nvm_otp_key_agent, a reactive agent.
//
// The request fifo (m_req_fifo) is given items (by nvm_otp_key_driver) when it sees requests. These can
// be consumed by a sequence, which can generate nvm_otp_key_rsp_seq_item responses which it feeds back
// to the sequencer.

class nvm_otp_key_sequencer extends dv_base_sequencer #(.ITEM_T (nvm_otp_key_rsp_seq_item),
                                                    .CFG_T  (nvm_otp_key_agent_cfg));
  `uvm_component_utils(nvm_otp_key_sequencer)

  // A request fifo that receives packets from the driver.
  uvm_tlm_analysis_fifo #(nvm_otp_key_req_seq_item) m_req_fifo;

  extern function new (string name, uvm_component parent);
endclass

function nvm_otp_key_sequencer::new (string name, uvm_component parent);
  super.new(name, parent);
  m_req_fifo = new("m_req_fifo", this);
endfunction
