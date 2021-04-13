// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Extends tl_host_single_seq to enable control over command integrity fields.
//
// This is useful to set up integrity error sequences,
// test execution of Instr/Data transactions, etc...
class cip_tl_host_single_seq extends tl_host_single_seq #(cip_tl_seq_item);

  `uvm_object_utils(cip_tl_host_single_seq)
  `uvm_object_new

  tlul_pkg::tl_type_e tl_type = DataType;

  virtual function void randomize_req(REQ req, int idx);
    super.randomize_req(req, idx);
    req.tl_type = tl_type;
  endfunction

endclass
