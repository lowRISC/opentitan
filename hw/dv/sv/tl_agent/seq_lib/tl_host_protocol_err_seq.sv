// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This seq will send an item that triggers d_error due to protocol violation
class tl_host_protocol_err_seq #(type REQ_T = tl_seq_item) extends tl_host_single_seq #(REQ_T);

  `uvm_object_param_utils(tl_host_protocol_err_seq #(REQ_T))
  `uvm_object_new

  // forever randomize the item until we find one that violates the TL protocol
  virtual function void randomize_req(REQ req, int idx);
    req.a_valid_delay = $urandom_range(min_req_delay, max_req_delay);
    req.a_valid_delay.rand_mode(0);
    req.randomize_a_chan_with_protocol_error();
  endfunction

endclass
