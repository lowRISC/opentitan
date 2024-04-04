// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Disable TL protocol related constraint on a_chan to create a fully customized tl_item for error
// cases
class tl_host_custom_seq #(type REQ_T = tl_seq_item) extends tl_host_single_seq #(REQ_T);

  `uvm_object_param_utils(tl_host_custom_seq #(REQ_T))
  `uvm_object_new

  virtual function void randomize_req(REQ req, int idx);
    control_addr_alignment = 1;
    control_rand_size      = 1;
    control_rand_opcode    = 1;
    req.disable_a_chan_protocol_constraint();
    super.randomize_req(req, idx);
  endfunction

endclass
