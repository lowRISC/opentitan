// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_cmderr_busy_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_busy_vseq)
  `uvm_object_new

  // Check that the busy field in abstractcs is as expected. It will be high if an abstract command
  // is currently executing.
  task check_busy(bit exp_busy);
    abstractcs_t abstractcs;
    read_abstractcs(abstractcs);
    `DV_CHECK_EQ(abstractcs.busy, exp_busy);
  endtask

  task body();
    uvm_reg_data_t rdata;

    clear_cmderr();

    // Tell the debug module to request a halt and tell it that we're halted (so that we can accept
    // the abstract command)
    request_halt();

    // Start an abstract command executing and check that it has started.
    csr_wr(.ptr(jtag_dmi_ral.command), .value(gen_read_register_cmd(0)));
    check_busy(1'b1);

    // Perform one of the operations that we expect to cause a "Busy" command error
    randcase
      1: csr_wr(.ptr(jtag_dmi_ral.command),         .value($urandom()));
      1: csr_wr(.ptr(jtag_dmi_ral.abstractcs),      .value($urandom()));
      1: csr_wr(.ptr(jtag_dmi_ral.abstractauto),    .value($urandom()));
      1: csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value($urandom()));
      1: csr_wr(.ptr(jtag_dmi_ral.progbuf[0]),      .value($urandom()));
      1: csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
      1: csr_rd(.ptr(jtag_dmi_ral.progbuf[0]),      .value(rdata));
    endcase

    // Check that the abstractcs register has a Busy value in its cmderr field
    check_cmderr(CmdErrBusy);

    // Complete the abstract command.
    //
    // This means writing to GOING and then HALTED
    csr_wr(.ptr(tl_mem_ral.going), .value(0));
    csr_wr(.ptr(tl_mem_ral.halted), .value(0));

    // Check that the abstract command has indeed completed (to make sure things don't get confused
    // if we chain them together)
    check_busy(1'b0);

    // Clear the cmderr field. This has access W1C and is 3 bits wide, so writing 3'b111 should
    // clear all the bits.
    csr_wr(.ptr(jtag_dmi_ral.abstractcs.cmderr), .value(7));

    // Check that we have managed to clear the command error (to leave things clean for following
    // sequences)
    check_cmderr(CmdErrNone);
  endtask

endclass : rv_dm_cmderr_busy_vseq
