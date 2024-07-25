// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_cmderr_exception_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_exception_vseq)
  `uvm_object_new

  task body();
    uvm_status_e wr_status;

    // Make sure that cmderr isn't currently set
    clear_cmderr();

    // Tell the debug module to request a halt and tell it that we're halted (so that we can accept
    // the abstract command)
    request_halt();

    // Start an abstract command executing
    csr_wr(.ptr(jtag_dmi_ral.command), .value(gen_read_register_cmd(0)));

    // Now tell rv_dm that there has been an exception while it was executing the command (by
    // writing over TL to the exception register)
    tl_mem_ral.exception.write(.status(wr_status), .value(1'b1));
    `DV_CHECK_EQ(wr_status, UVM_IS_OK)

    // This should have been reflected in the cmderr field of abstractcs.
    check_cmderr(CmdErrorException);

    // Clear cmderr again (to avoid leaving things in a mess for any following sequence)
    clear_cmderr();
  endtask : body

endclass : rv_dm_cmderr_exception_vseq
