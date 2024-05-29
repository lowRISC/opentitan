// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//halt/resume/whereto test
class rv_dm_halt_resume_whereto_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_halt_resume_whereto_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  // Pretend to be the hart entering debug mode and write the ID (hartsel) to the HALTED register to
  // indicate that we are halted.
  task write_halted(input int unsigned hartsel);
    csr_wr(.ptr(tl_mem_ral.halted), .value(hartsel));
  endtask

  // Read the abstractcs register over DMI
  task read_abstractcs(output abstractcs_t ret);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(rdata));
    ret = dm::abstractcs_t'(rdata);
  endtask

  // Check whether the debugger reports itself to be busy through the abstractcs register
  task check_busy(bit exp_busy);
    abstractcs_t abstractcs;
    read_abstractcs(abstractcs);
    `DV_CHECK_EQ(abstractcs.busy, exp_busy);
  endtask

  // Read a FLAGS register over TL-UL and check it matches the expected state
  task check_flags(input bit exp_resume, input bit exp_go, input int unsigned hartsel);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(tl_mem_ral.flags[hartsel]), .value(rdata));
    `DV_CHECK_EQ(rdata, {exp_resume, exp_go})
  endtask

  // Read the WHERETO register over TL-UL and check it contains the expected instruction, which
  // should be a relative jump instruction (jal) pointing at the first instruction to run. This
  // should be the first instruction in the abstract command, which is stored at "ProgBufBaseAddr"
  // (the start of the program buffer).
  task check_whereto();
    // The address of the start of the program buffer is an implementation detail of the pulp debug
    // module: we've picked it out of the code to match. Similarly, the "WhereTo instruction" lies
    // at an address which is an implementation detail (WhereToAddr in dm_mem.sv).
    bit [31:0] prog_buf_addr = dm::DataAddr - 4*dm::ProgBufSize;
    bit [31:0] whereto_addr = 'h300;

    uvm_reg_data_t rdata;
    csr_rd(.ptr(tl_mem_ral.whereto), .value(rdata));
    `DV_CHECK_EQ(rdata, dm::jal(.rd(0), .imm(prog_buf_addr - whereto_addr)))
  endtask

  // Construct a "read register" abstract command.
  function bit [31:0] read_register_cmd(bit [15:0] regno);
    dm::ac_ar_cmd_t ar_cmd = '0;
    dm::command_t cmd;

    ar_cmd.aarsize  = 3'h2;
    ar_cmd.postexec = 1'b1;
    ar_cmd.regno    = regno;

    cmd.cmdtype = dm::AccessRegister;
    cmd.control = ar_cmd;
    return cmd;
  endfunction

  task body();
    int unsigned hartsel = 0;

    repeat (2) begin
      request_halt();

      // Send an abstract command over DMI (read a register)
      csr_wr(.ptr(jtag_dmi_ral.command), .value(read_register_cmd(16'h40)));

      check_busy(1'b1);

      // Check the debugger's state machine is currently in the Go state with no resume flag.
      check_flags(.exp_resume(0), .exp_go(1), .hartsel(0));

      // Write to the "going" address to tell the debugger the core is executing again. The actual
      // value that is written doesn't matter.
      csr_wr(.ptr(tl_mem_ral.going), .value(0));

      check_busy(1'b1);

      // Check that WHERETO points at the expected address
      check_whereto();

      // Write the expected value to HALTED. This should be the ID of the hart that is halting
      write_halted(hartsel);

      // Now the hart has responded to say that it's entering debug mode, the debugger shouldn't
      // think that it's busy any more.
      check_busy(1'b0);

      // Write over DMI to clear HALTREQ and then set RESUMEREQ. At this point, we've stopped asking
      // to halt and now want to ask the hart to resume.
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(0));
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.resumereq), .value(1));

      // Now we've told the debugger to ask the hart to resume, the debugger should say it's busy
      // until the hart responds to say that it is indeed resuming.
      check_busy(1'b1);

      // Check that the resume signal is being sent from the debugger to the hart.
      check_flags(.exp_resume(1), .exp_go(0), .hartsel(hartsel));

      // Finally respond (as the hart) to tell the debugger that we are resuming.
      csr_wr(.ptr(tl_mem_ral.resuming), .value(hartsel));

      // Now that the hart has responded, the debugger should no longer be busy.
      check_busy(1'b0);
    end
  endtask

endclass: rv_dm_halt_resume_whereto_vseq
