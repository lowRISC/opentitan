// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// command error exception test vseq
class rv_dm_cmderr_exception_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_exception_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    // Verify that the cmderr should be AbstractCmdErrException,
    // if an excepton occurred while executing the command.
    write_chk(.ptr(tl_mem_ral.exception), .cmderr(AbstractCmdErrException), .command(32'h00231000));
  endtask : body

endclass : rv_dm_cmderr_exception_vseq
