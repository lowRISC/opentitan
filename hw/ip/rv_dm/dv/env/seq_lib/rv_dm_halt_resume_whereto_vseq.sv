// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//halt/resume/whereto test
class rv_dm_halt_resume_whereto_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_halt_resume_whereto_vseq)
  `uvm_object_new

  // Pretend to be the hart entering debug mode and write the ID (hartsel) to the HALTED register to
  // indicate that we are halted.
  task write_halted(input int unsigned hartsel);
    csr_wr(.ptr(tl_mem_ral.halted), .value(hartsel));
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
  // should be the first instruction in the abstract command, which is either stored at
  // AbstractCmdBaseAddr or (as a shortcut) it might be stored at "ProgBufBaseAddr" (the start of
  // the program buffer). Here, we don't model which case we're in, so we just check that it points
  // to one of those addresses.
  task check_whereto();
    // The address of the start of the program buffer is an implementation detail of the pulp debug
    // module: we've picked it out of the code to match, and the same for the offset to the start of
    // the abstract command. Similarly, the "WhereTo instruction" lies at an address which is an
    // implementation detail (WhereToAddr in dm_mem.sv).
    bit [31:0] prog_buf_addr = dm::DataAddr - 4*dm::ProgBufSize;
    bit [31:0] abs_cmd_addr = prog_buf_addr - 4*10;
    bit [31:0] whereto_addr = 'h300;

    logic [31:0] prog_buf_jal = dm::jal(.rd(0), .imm(prog_buf_addr - whereto_addr));
    logic [31:0] abs_cmd_jal = dm::jal(.rd(0), .imm(abs_cmd_addr - whereto_addr));

    uvm_reg_data_t rdata;
    csr_rd(.ptr(tl_mem_ral.whereto), .value(rdata));
    `DV_CHECK(rdata inside {prog_buf_jal, abs_cmd_jal},
              $sformatf({"The whereto register reads as %0x, which is not either ",
                         "of the jumps we expected (%0x, %0x)"},
                        rdata, prog_buf_jal, abs_cmd_jal))
  endtask

  // Construct an "access register" abstract command.
  function bit [31:0] access_register_cmd();
    dm::ac_ar_cmd_t ar_cmd = '0;
    dm::command_t   cmd;
    bit [3:0]       regno;
    bit             write, transfer;

    regno = $urandom_range(0, 16'h3fff);

    // We want to generate writes with or without the transfer flag. We also want to generate reads
    // (and occasionally set the transfer flag, even though it won't actually do anything)
    write = $urandom_range(0, 1);
    randcase
      2:       transfer = 1'b1;
      write*2: transfer = 1'b0;
      1:       transfer = 1'b0;
    endcase

    ar_cmd.aarsize  = 3'h2;
    ar_cmd.postexec = $urandom_range(0, 1);
    ar_cmd.transfer = transfer;
    ar_cmd.write    = write;
    ar_cmd.regno    = regno;

    cmd.cmdtype = dm::AccessRegister;
    cmd.control = ar_cmd;
    return cmd;
  endfunction

  task body();
    int unsigned hartsel = 0;

    request_halt();

    // Send an abstract command over DMI (access a register)
    csr_wr(.ptr(jtag_dmi_ral.command), .value(access_register_cmd()));

    check_busy(1'b1);

    // Check the debug module's state machine is currently in the Go state with no resume flag.
    check_flags(.exp_resume(0), .exp_go(1), .hartsel(0));

    // Write to the "going" address to tell the debug module the core is executing again. The actual
    // value that is written doesn't matter.
    csr_wr(.ptr(tl_mem_ral.going), .value(0));

    check_busy(1'b1);

    // Check that WHERETO points at the expected address
    check_whereto();

    // Write the expected value to HALTED. This should be the ID of the hart that is halting
    write_halted(hartsel);

    // Now the hart has responded to say that it's entering debug mode, the debug module shouldn't
    // think that it's busy any more.
    check_busy(1'b0);

    // Write over DMI to clear HALTREQ and then set RESUMEREQ. At this point, we've stopped asking
    // to halt and now want to ask the hart to resume.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(0));
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.resumereq), .value(1));

    // Now we've told the debug module to ask the hart to resume, the debug module should say it's
    // busy until the hart responds to say that it is indeed resuming.
    check_busy(1'b1);

    // Check that the resume signal is being sent from the debug module to the hart.
    check_flags(.exp_resume(1), .exp_go(0), .hartsel(hartsel));

    // Finally respond (as the hart) to tell the debug module that we are resuming.
    csr_wr(.ptr(tl_mem_ral.resuming), .value(hartsel));

    // Now that the hart has responded, the debug module should no longer be busy.
    check_busy(1'b0);

    // Finally (as the debugger) write 1 to resumereq to drop the resume request: it has now done
    // its job!
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.resumereq), .value(1));
  endtask

endclass: rv_dm_halt_resume_whereto_vseq
