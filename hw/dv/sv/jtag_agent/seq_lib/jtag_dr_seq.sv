// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to drive data register in JTAG.
class jtag_dr_seq extends jtag_ir_seq;

  `uvm_object_utils(jtag_dr_seq)
  `uvm_object_new

  rand logic [JTAG_DRW-1:0] dr;
  rand uint dr_len;

  virtual function void randomize_req(jtag_item req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len    == 0;
        dr_len    == local::dr_len;
        ir        == 0;
        dr        == local::dr;
        select_ir == 0;
    )
  endfunction
endclass
