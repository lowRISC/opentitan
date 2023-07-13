// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) PC.CTRL_FLOW.REDUN.

class otbn_ctrl_redun_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_ctrl_redun_vseq)
  `uvm_object_new

  bit have_injected_error;

  task body();
    do_end_addr_check = 0;

    // Run the otbn_single_vseq body, which runs a single OTBN application to completion. At the
    // same time, try to inject an error and check that the RTL (and model) both spot the error. If
    // we didn't find a good moment to inject the error, fail the test: sadly, it hasn't actually
    // tested anything.
    have_injected_error = 1'b0;
    fork
      begin
        super.body();
      end
      begin
        inject_redun_err();
      end
    join_any

    if (!have_injected_error) begin
      `uvm_fatal(`gfn, "Never found a time to inject an error.")
    end

  endtask: body

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
      // Injecting error on ispr_addr during a write
      0: begin
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_addr_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_wr_en");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_addr));
        // Mask to corrupt 1 to 2 bits of the ispr addr
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
        bad_addr = good_addr ^ mask;
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_addr) == 1);
      end
      // Injecting error on ispr_addr during a read
      1: begin
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_addr_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_alu_bignum.ispr_rd_en_i");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_addr));
        // Mask to corrupt 1 to 2 bits of the ispr addr
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
        bad_addr = good_addr ^ mask;
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_addr) == 1);
      end
      // injecting error on opcode
      2: begin
        logic [3:0] good_op, bad_op;
        err_path = "tb.dut.u_otbn_core.u_otbn_alu_bignum.operation_i.op";
        wait_for_flag("tb.dut.u_otbn_core.alu_bignum_operation_valid");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_op));
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_op,
                                           bad_op != good_op;
                                           bad_op != otbn_pkg::AluOpBignumNone;);
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_op) == 1);
      end
      // injecting error on lsu_addr_en
      3: begin
        bit choose_err;
        otbn_pkg::insn_dec_shared_t insn_dec_shared_i;
        err_path = "tb.dut.u_otbn_core.u_otbn_controller.insn_dec_shared_i";
        wait_for_flag("tb.dut.u_otbn_core.u_otbn_controller.insn_valid_i");
        `DV_CHECK_FATAL(uvm_hdl_read(err_path, insn_dec_shared_i));
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_err)
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
      // injects error into otbn_core
      4: begin
        bit [1:0] choose_err;
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 1000));
        wait_for_flag("tb.dut.u_otbn_core.insn_valid");
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(choose_err, choose_err inside {[0:2]};)
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
      // injects error into otbn_mac_bignum
      5: begin
        bit mac_en;
        bit choose_err;
        `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute)
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
        `DV_CHECK_STD_RANDOMIZE_FATAL(choose_err)
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
      // injects errors into otbn_rf_bignum
      6: begin
        bit [1:0] choose_err;
        bit [4:0] addr;
        bit [4:0] mask;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(choose_err, choose_err inside {[0:2]};)
        case(choose_err)
          0: begin
            err_path = "tb.dut.u_otbn_core.u_otbn_rf_bignum.wr_addr_i[4:0]";
            wait_for_flag("tb.dut.u_otbn_core.u_otbn_rf_bignum.wr_en_i[1:0]");
            `DV_CHECK_FATAL(uvm_hdl_read(err_path, addr));
            `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
            addr = addr ^ mask;
            `DV_CHECK_FATAL(uvm_hdl_force(err_path, addr) == 1);
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
