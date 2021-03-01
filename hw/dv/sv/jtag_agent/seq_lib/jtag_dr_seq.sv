// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A dmi access sequence to drive a single CSR read or write
class jtag_dr_seq extends jtag_ir_seq;

  rand logic [JTAG_IRW-1:0] dr;

  `uvm_object_utils(jtag_dr_seq)
  `uvm_object_new

  virtual function randomize_req(jtag_item req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len == DMI_IRW;
        dr_len == DMI_DRW;
        dr        == local::dr;
        select_dr == 1;
    )
  endfunction
endclass
