// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Extends tl_host_single_seq to enable control over command integrity fields.
//
// This is useful to set up integrity error sequences,
// test execution of Instr/Data transactions, etc...
class cip_tl_host_single_seq extends tl_host_single_seq #(cip_tl_seq_item);

  `uvm_object_utils(cip_tl_host_single_seq)
  `uvm_object_new

  mubi4_t instr_type                   = MuBi4False;
  tl_intg_err_e       tl_intg_err_type = TlIntgErrNone;

  virtual function void randomize_req(REQ req, int idx);
    super.randomize_req(req, idx);

    // set tl_intg_err_type first, as set_instr_type will trigger re-calculating integrity based on
    // the TLUL info and err_type
    req.tl_intg_err_type = tl_intg_err_type;
    req.set_instr_type(instr_type);
  endfunction

endclass
