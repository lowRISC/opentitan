// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_cmderr_not_supported_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_not_supported_vseq)
  `uvm_object_new

  // Generate an abstract command that will trigger a "not supported" error because it's cmdtype is
  // unknown.
  function command_t gen_bogus_abstract_cmd();
    command_t cmd;
    `DV_CHECK_STD_RANDOMIZE_FATAL(cmd)

    if (cmd.cmdtype inside {AccessRegister, QuickAccess, AccessMemory}) begin
      cmd.cmdtype = cmd_e'(cmd.cmdtype + 3);
    end

    return cmd;
  endfunction

  // Check that the cmderr field in abstractcs is as expected. If the system is in reset, skip the
  // check.
  task check_cmderr(cmderr_e cmderr_exp);
    abstractcs_t abstractcs;
    read_abstractcs(abstractcs);
    if (cfg.clk_rst_vif.rst_n) `DV_CHECK_EQ(abstractcs.cmderr, cmderr_exp);
  endtask

  task body();
    // Check that there isn't currently any command error (if there is, it will be sticky and we
    // won't be able to change it to CmdErrNotSupported)
    check_cmderr(CmdErrNone);

    // Tell the debug module to request a halt and tell it that we're halted (so that we can accept
    // the abstract command)
    request_halt();

    if (!cfg.clk_rst_vif.rst_n) return;

    // Ask to start a (bogus) abstract command. This won't actually start, but should cause a
    // command error flag.
    csr_wr(.ptr(jtag_dmi_ral.command), .value(gen_bogus_abstract_cmd()));

    // Check that the cmderr field of the abstractcs register is now CmdErrNotSupported
    check_cmderr(CmdErrNotSupported);

    if (!cfg.clk_rst_vif.rst_n) return;

    // Clear the cmderr field. This has access W1C and is 3 bits wide, so writing 3'b111 should
    // clear all the bits.
    csr_wr(.ptr(jtag_dmi_ral.abstractcs.cmderr), .value(7));

    // Check that we have managed to clear the command error (to leave things clean for following
    // sequences)
    check_cmderr(CmdErrNone);
  endtask

endclass : rv_dm_cmderr_not_supported_vseq
