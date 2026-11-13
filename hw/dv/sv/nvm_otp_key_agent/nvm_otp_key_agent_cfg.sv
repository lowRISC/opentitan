// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class nvm_otp_key_agent_cfg extends dv_reactive_agent_cfg;

  virtual nvm_otp_key_if vif;

  // If set, the agent starts nvm_otp_key_device_seq on its sequencer at the start of the run
  // phase, so that every request is answered without the testbench having to start a sequence.
  // Clear it to start a different sequence instead.
  bit start_default_seq = 1'b1;

  // Range of nvm_otp_key_item::ack_delay used by nvm_otp_key_device_seq. A real otp_ctrl's
  // response latency isn't fixed, so the DUT must tolerate any value here.
  int unsigned ack_delay_min = 0;
  int unsigned ack_delay_max = 5;

  `uvm_object_utils_begin(nvm_otp_key_agent_cfg)
    `uvm_field_int(start_default_seq, UVM_DEFAULT)
    `uvm_field_int(ack_delay_min,     UVM_DEFAULT | UVM_DEC)
    `uvm_field_int(ack_delay_max,     UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  extern function new(string name = "");
endclass : nvm_otp_key_agent_cfg

function nvm_otp_key_agent_cfg::new(string name = "");
  super.new(name);
  // The DUT is always the requester, so the agent always plays the responder (otp_ctrl). The
  // monitor passes new requests to the device sequence through the sequencer's request FIFO.
  if_mode      = Device;
  has_req_fifo = 1'b1;
endfunction : new
