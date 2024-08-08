// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) PC.CTRL_FLOW.REDUN.

class otbn_ctrl_redun_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_ctrl_redun_vseq)
  `uvm_object_new

  bit have_injected_error;

  task body();
    do_end_addr_check = 0;

    // Try to run an OTBN application to completion, injecting an error in the middle. We might be
    // unlucky and fail to find a good time to inject an error. In that case, try_once will tidy up
    // and we can try again.
    repeat (4) begin
      try_once();
      if (have_injected_error) break;
    end
    if (!have_injected_error) begin
      `uvm_fatal(`gfn, "Never found a time to inject an error.")
    end

  endtask: body

  // Run the otbn_single_vseq body, which runs a single OTBN application to completion. At the
  // same time, try to inject an error and check that the RTL (and model) both spot the error.
  task try_once();
    fork begin : isolation_fork
      fork
        // Run the otbn_single_vseq body
        super.body();
        // Try to inject an error
        inject_redun_err();
      join_any

      // If have_injected_error is false then super.body() has run to completion and we should kill
      // the inject_redun_err process (since it isn't going to find a time now). If it is true then
      // we managed to inject an error. In that case, wait until super.body() has run to completion,
      // which lets the run_otbn task tidy up properly.
      if (!have_injected_error) disable fork;
      else wait fork;
    end join
  endtask

  // Wait until the value at path becomes nonzero
  task wait_for_flag(string path);
    // Initialise flag to zero. With some simulators (one version of Xcelium, at least), it seems
    // that the call to uvm_hdl_read might leave its destination set to X. The HDL path exists and
    // the signal is not X, so this is rather confusing. Initialising flag to zero before calling
    // uvm_hdl_read seems to fix the behaviour.
    uvm_hdl_data_t flag = 0;
    `DV_SPINWAIT(do begin
                   @(cfg.clk_rst_vif.cb);
                   `DV_CHECK_FATAL(uvm_hdl_read(path, flag) == 1);
                 end while(!flag);)
  endtask

  function void report_err_type(string desc);
    `uvm_info(`gfn, $sformatf("Injecting an error of type: %s", desc), UVM_MEDIUM)
  endfunction

  task inject_redun_err();
    bit [3:0] err_type;
    string err_path;
    bit [3:0] good_addr;
    bit [3:0] bad_addr;
    bit [3:0] mask;
    bit [31:0] err_val = 32'd1 << 20;

    // We're doing something evil and forcing a signal inside the design. We expect the design to
    // notice that something went wrong and lock itself and we test for that. However, the design
    // RTL has some assertions that are rendered false by the forcing that we do. To avoid killing
    // the simulation with the failed assertion, turn them off here, and turn them on again at the
    // end of this task.
    $assertoff(0, "tb.dut.g_secure_wipe_assertions");

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_type, err_type inside {[0:6]};)
    case(err_type)
      0: begin
        report_err_type("error on ispr_addr during a write");
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_addr_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_wr_en");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_addr));
        // Mask to corrupt 1 to 2 bits of the ispr addr
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
        bad_addr = good_addr ^ mask;
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_addr) == 1);
      end
      1: begin
        report_err_type("error on ispr_addr during a read");
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_addr_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_rd_en_i");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_addr));
        // Mask to corrupt 1 to 2 bits of the ispr addr
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
        bad_addr = good_addr ^ mask;
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_addr) == 1);
      end
      2: begin
        logic [3:0] good_op, bad_op;
        logic       selected_flags_C;
        bit         avoid_addc = 1'b0;

        string alu_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum";
        string op_path = {alu_path, ".operation_i.op"};
        string op_valid_path = {alu_path, ".operation_valid_i"};
        string carry_path = {alu_path, ".selected_flags.C"};

        report_err_type("error in opcode on the bignum side");
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.operation_i.op";

        // We want to inject an error when the bignum ALU is performing an operation, so its
        // operation_valid_i flag should be high, and this should be the opcode for a genuine
        // operation (less than or equal to AluOpBignumNot).
        while (1) begin
          wait_for_flag(op_valid_path);
          `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_op))
          if (good_op <= otbn_pkg::AluOpBignumNot)
            break;
          // If the opcode doesn't specify a known operation, we'll need to wait a bit longer. Go
          // around again.
        end

        // We also know that the pre-decode check won't spot conversions between add/addc and
        // sub/subb if the selected flags register happens to be zero (because the change in opcode
        // won't actually have any effect). We want to constrain the randomisation to avoid doing
        // one of those conversions if we're in that situation.
        //
        //  - Do this by adding an avoid_addc flag that avoids a conversion between add/addc when
        //    the carry flag is zero. (This also applies to subtractions: see the point below)
        //
        // It also isn't strict enough to spot conversions between addX and subX for any X. We can
        // avoid requiring that it should by adding two constraints:
        //
        //  - Constraining the difference between good_op and bad_op not to be 3. Because there are
        //    three add instructions this guarantees we won't convert between addX and subX for any
        //    X.
        //
        //  - Extend the avoid_addc flag (which would normally avoid trying to distinguish between
        //    add/addc, sub/subb when the carry flag was zero) so that they apply to both either
        //    additions or subtractions. This will avoid e.g. converting between add and subb.
        `DV_CHECK_FATAL(uvm_hdl_read(carry_path, selected_flags_C))
        if (!selected_flags_C) begin
          if (good_op inside {otbn_pkg::AluOpBignumAdd, otbn_pkg::AluOpBignumAddc,
                              otbn_pkg::AluOpBignumSub, otbn_pkg::AluOpBignumSubb}) begin
            avoid_addc = 1'b1;
          end
        end

        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_op,
                                           bad_op != good_op;
                                           bad_op != otbn_pkg::AluOpBignumNone;
                                           avoid_addc -> (bad_op != otbn_pkg::AluOpBignumAdd &&
                                                          bad_op != otbn_pkg::AluOpBignumAddc &&
                                                          bad_op != otbn_pkg::AluOpBignumSub &&
                                                          bad_op != otbn_pkg::AluOpBignumSubb);
                                           bad_op != good_op + 3; good_op != bad_op + 3;)

        `uvm_info(`gfn,
                  $sformatf("Forcing %0s from %0d to %0d", err_path, good_op, bad_op),
                  UVM_MEDIUM)
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_op) == 1);
      end
      3: begin
        bit choose_err;
        otbn_pkg::insn_dec_shared_t insn_dec_shared_i;
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_err)

        report_err_type($sformatf("error on lsu_addr_en (choose_err = %0d)", choose_err));

        err_path = "tb.dut.u_otbn_core.u_otbn_controller.insn_dec_shared_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_controller.insn_valid_i");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, insn_dec_shared_i));
        case(choose_err)
          0: begin
            insn_dec_shared_i.ld_insn = !insn_dec_shared_i.ld_insn;
          end
          1: begin
            insn_dec_shared_i.st_insn = !insn_dec_shared_i.st_insn;
          end
          default: begin
            `uvm_fatal(`gfn, "issue with randomization")
          end
        endcase
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, insn_dec_shared_i) == 1);
      end
      4: begin
        bit [1:0] choose_err;
        int unsigned num_clks = $urandom_range(10, 100);
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(choose_err, choose_err inside {[0:2]};)

        report_err_type($sformatf("core error (choose_err = %0d, after %0d clocks)",
                                  choose_err, num_clks));
        cfg.clk_rst_vif.wait_clks(num_clks);
        wait_for_flag("tb.dut.u_otbn_core.insn_valid");
        case(choose_err)
          0: begin
            bit [31:0] bad_rf_ren_a;
            bit [31:0] good_rf_ren_a;
            err_path = "tb.dut.u_otbn_core.rf_predec_bignum.rf_ren_a";
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_rf_ren_a));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_rf_ren_a,  $countones(bad_rf_ren_a) == 1;
                                               bad_rf_ren_a != good_rf_ren_a;)
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_rf_ren_a) == 1);
          end
          1: begin
            bit [31:0] bad_rf_ren_b;
            bit [31:0] good_rf_ren_b;
            err_path = "tb.dut.u_otbn_core.rf_predec_bignum.rf_ren_b";
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_rf_ren_b));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_rf_ren_b,  $countones(bad_rf_ren_b) == 1;
                                               bad_rf_ren_b != good_rf_ren_b;)
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_rf_ren_b) == 1);
          end
          2: begin
            bit [8:0] bad_ispr_rd_en;
            bit [8:0] good_ispr_rd_en;
            err_path = "tb.dut.u_otbn_core.ispr_predec_bignum.ispr_rd_en";
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_ispr_rd_en));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_ispr_rd_en,  $countones(bad_ispr_rd_en) == 1;
                                               bad_ispr_rd_en != good_ispr_rd_en;)
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_ispr_rd_en) == 1);
          end
          default: begin
            `uvm_fatal(`gfn, "issue with randomization")
          end
        endcase
      end
      5: begin
        bit mac_en;
        bit choose_err;
        int unsigned num_clks = $urandom_range(10, 100);
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_err)

        report_err_type($sformatf("error in otbn_mac_bignum (choose_err=%0d, after %0d clocks)",
                                  choose_err, num_clks));

        `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute)
        cfg.clk_rst_vif.wait_clks(num_clks);
        // Wait for valid instruction, because `otbn_core` only propagates bignum MAC predec errors
        // for valid instructions.
        wait_for_flag("tb.dut.u_otbn_core.insn_valid");
        case(choose_err)
          0: begin
            err_path = "tb.dut.u_otbn_core.u_otbn_mac_bignum.mac_en_i";
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, mac_en));
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, !mac_en) == 1);
          end
          1: begin
            bit zero_acc;
            err_path = "tb.dut.u_otbn_core.u_otbn_mac_bignum.operation_i.zero_acc";
            wait_for_flag("tb.dut.u_otbn_core.u_otbn_mac_bignum.mac_en_i");
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, zero_acc));
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, !zero_acc) == 1);
          end
          default: begin
            `uvm_fatal(`gfn, "issue with randomization")
          end
        endcase
      end
      6: begin
        bit [1:0] choose_err;
        bit [4:0] addr;
        bit [4:0] mask;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(choose_err, choose_err inside {[0:2]};)

        report_err_type($sformatf("error in otbn_rf_bignum (choose_err=%0d)", choose_err));
        case(choose_err)
          0: begin
            err_path = "tb.dut.u_otbn_core.u_otbn_rf_bignum.wr_addr_i[4:0]";
            wait_for_flag("tb.dut.u_otbn_core.u_otbn_rf_bignum.wr_en_i[1:0]");
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, addr));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
            addr = addr ^ mask;
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, addr) == 1);

            // At this point, we've forced the signal, which should cause the design to detect and
            // error and lock up. For this signal, the detected error goes through a register stage,
            // so we need to wait an extra cycle before telling the model to lock (and clear its
            // insn_cnt register)
            cfg.clk_rst_vif.wait_clks(1);
          end
          1: begin
            err_path = "tb.dut.u_otbn_core.u_otbn_rf_bignum.rd_addr_a_i";
            wait_for_flag("tb.dut.u_otbn_core.u_otbn_rf_bignum.rd_en_a_i");
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, addr));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
            addr = addr ^ mask;
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, addr) == 1);
          end
          2: begin
            err_path = "tb.dut.u_otbn_core.u_otbn_rf_bignum.rd_addr_b_i";
            wait_for_flag("tb.dut.u_otbn_core.u_otbn_rf_bignum.rd_en_b_i");
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, addr));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
            addr = addr ^ mask;
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, addr) == 1);
          end
          default: begin
            `uvm_fatal(`gfn, "issue with randomization")
          end
        endcase
      end
      default: begin
        `uvm_fatal(`gfn, "issue with randomization")
      end
    endcase
    `uvm_info(`gfn, "injecting bad internal state error into ISS", UVM_HIGH)
    have_injected_error = 1'b1;
    cfg.model_agent_cfg.vif.send_err_escalation(err_val);
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
    `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1);
    reset_if_locked();

    // Turn the secure wipe assertions on again (there's a note above the $assertoff call earlier
    // which explains what we're doing).
    $asserton(0, "tb.dut.g_secure_wipe_assertions");
  endtask

endclass : otbn_ctrl_redun_vseq
