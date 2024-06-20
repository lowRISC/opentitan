// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_cmderr_busy_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_busy_vseq)
  `uvm_object_new

  // Generate an abstract command that tries to read the specified register
  function command_t gen_read_register_cmd(bit [15:0] regno);
    command_t cmd;
    ac_ar_cmd_t ar_cmd = '0;

    ar_cmd.aarsize = 2; // Access lower 32 bits
    ar_cmd.aarpostincrement = 0;
    ar_cmd.postexec = 0;
    ar_cmd.transfer = 0;
    ar_cmd.write = 0;
    ar_cmd.regno = regno;

    cmd.cmdtype = AccessRegister;
    cmd.control = ar_cmd;
    return cmd;
  endfunction

  // Check that the busy field in abstractcs is as expected. It will be high if an abstract command
  // is currently executing.
  task check_busy(bit exp_busy);
    abstractcs_t abstractcs;
    read_abstractcs(abstractcs);
    `DV_CHECK_EQ(abstractcs.busy, exp_busy);
  endtask

  // Check that the cmderr field in abstractcs is as expected
  task check_cmderr(cmderr_e cmderr_exp);
    abstractcs_t abstractcs;
    read_abstractcs(abstractcs);
    `DV_CHECK_EQ(abstractcs.cmderr, cmderr_exp);
  endtask

  task body();
    uvm_reg_data_t rdata;

    // Check that there isn't currently any command error (if there is, it will be sticky and we
    // won't be able to change it to CmdErrBusy)
    check_cmderr(CmdErrNone);

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
