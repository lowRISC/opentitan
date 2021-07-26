// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class csrng_smoke_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_smoke_vseq)

  `uvm_object_new

  task body();
    ral.ctrl.read_int_state.set(4'hA);
    // Wait for CSRNG cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    // Write CSRNG Cmd_Req - Instantiate Command
    wr_cmd_req(.acmd(csrng_pkg::INS), .clen(0), .flags(1), .glen(0));

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.cs_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));

    // Write CSRNG Cmd_Req Register - Generate Command
    wr_cmd_req(.acmd(csrng_pkg::GEN), .clen(0), .flags(0), .glen(1));

    // Wait for CSRNG genbits_vld
    csr_spinwait(.ptr(ral.genbits_vld.genbits_vld), .exp_data(1'b1));

    // TODO: remove code below and use scoreboard values
    //Read CSRNG genbits
//    for (int i = 0; i < 4; i++) begin
//      csr_rd_check(.ptr(ral.genbits.genbits), .compare_value(ZERO_SEED_GENBITS[i]));
//    end
      csr_rd_check(.ptr(ral.genbits.genbits), .compare_value(32'h735b27a0));
      csr_rd_check(.ptr(ral.genbits.genbits), .compare_value(32'h497b246f));
      csr_rd_check(.ptr(ral.genbits.genbits), .compare_value(32'h9a8f9420));
      csr_rd_check(.ptr(ral.genbits.genbits), .compare_value(32'h91618fe9));

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.cs_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask : body

endclass : csrng_smoke_vseq
