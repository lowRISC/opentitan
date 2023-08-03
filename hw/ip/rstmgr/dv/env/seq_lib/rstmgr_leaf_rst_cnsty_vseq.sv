// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This tests each leaf reset consistency checkers.
//
// For resets out of
// 1 - low power entry reset
// 2 - hw req reset
// 3 - sw reset
// Create reset consistency errors in the current leaf, and check that a
// fatal_cnsty_fault alert is generated.
class rstmgr_leaf_rst_cnsty_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_leaf_rst_cnsty_vseq)

  `uvm_object_new

  int    cycles_to_check = 7;
  int    error_pos;
  int    my_pos;
  rand int cycles_reset_width;
  rand int cycles_child_reset_width;
  rand int cycles_in_apply_resets;
  rand int cycles_to_child_reset;
  rand int cycles_to_child_release;
  rand int cycles_to_parent_reset;
  rand int cycles_to_parent_release;
  rand int cycles_to_sw_reset;
  rand int cycles_to_sw_release;

  constraint rstreqs_non_zero_c {rstreqs != '0;}
  constraint sw_rst_regwen_non_trivial_c {sw_rst_regwen != '0 && sw_rst_regwen != '1;}
  constraint sw_rst_some_reset_n_c {sw_rst_regwen & ~sw_rst_ctrl_n != '0;}

  constraint cycles_reset_width_c {cycles_reset_width inside {[2 : 10]};}
  constraint cycles_child_reset_width_c {cycles_child_reset_width inside {[2 : 10]};}
  constraint cycles_in_apply_resets_c {cycles_in_apply_resets inside {[5 : 25]};}
  constraint cycles_to_child_reset_c {cycles_to_child_reset inside {[3 : 8]};}
  constraint cycles_to_child_release_c {cycles_to_child_release inside {[3 : 6]};}
  constraint cycles_to_parent_reset_c {cycles_to_parent_reset inside {[2 : 8]};}
  constraint cycles_to_parent_release_c {cycles_to_parent_release inside {[3 : 6]};}
  constraint cycles_to_sw_reset_c {cycles_to_sw_reset inside {[2 : 8]};}
  constraint cycles_to_sw_release_c {cycles_to_sw_release inside {[3 : 6]};}

  // There is an extra POR reset when the consistency failure is triggered due to apply_reset.
  int maybe_por_reset;

  task body();
    for (int i = 0; i < LIST_OF_LEAFS.size(); ++i) begin
      string leaf_path = {"tb.dut.", LIST_OF_LEAFS[i], ".gen_rst_chk.u_rst_chk"};
      error_pos = $urandom_range(1, 3);
      my_pos = 0;
      `uvm_info(`gfn, $sformatf("Round %0d %s pos:%0d", i, leaf_path, error_pos), UVM_MEDIUM)
      // Get a clean slate for reset_info.
      csr_wr(.ptr(ral.reset_info), .value('1));

      fork
        unexpected_child_activity(leaf_path);
        begin
          int expected;
          set_pos_and_wait();
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);
          // Send low power entry reset.
          send_lowpower_reset();
          expected = 1 << ral.reset_info.low_power_exit.get_lsb_pos();

          check_reset_info(maybe_por_reset | expected, "expected reset_info to indicate low power");
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

          csr_wr(.ptr(ral.reset_info), .value('1));
          cfg.io_div4_clk_rst_vif.wait_clks(10);

          // Send HwReq.
          // Enable alert_info and cpu_info capture.
          set_pos_and_wait();
          `DV_CHECK_RANDOMIZE_FATAL(this)
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);
          expected = rstreqs << ral.reset_info.hw_req.get_lsb_pos();
          send_hw_reset(rstreqs);
          check_reset_info(maybe_por_reset | expected, $sformatf(
                           "expected reset_info to match hw_req 0x%x", expected));
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

          csr_wr(.ptr(ral.reset_info), .value('1));

          set_pos_and_wait();
          `DV_CHECK_RANDOMIZE_FATAL(this)
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

          // Send sw reset.
          csr_wr(.ptr(ral.reset_req), .value(MuBi4True));
          send_sw_reset();
          expected = 1 << ral.reset_info.sw_reset.get_lsb_pos();
          check_reset_info(maybe_por_reset | expected, "Expected reset_info to indicate sw reset");
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 0);
          csr_wr(.ptr(ral.reset_info), .value('1));
        end
      join
    end
  endtask : body

  task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

  task send_unexpected_child_reset(string path);
    `uvm_info(`gfn, "unexpected child reset start", UVM_MEDIUM)
    // clear all
    set_leaf_reset(.path({path, ".parent_rst_ni"}), .value(1), .cycles(0));
    set_leaf_reset(.path({path, ".sw_rst_req_i"}), .value(0), .cycles(0));
    set_leaf_reset(.path({path, ".child_rst_ni"}), .value(1), .cycles(0));

    cfg.scoreboard.set_exp_alert("fatal_cnsty_fault", 1, 20);

    // assert child reset
    set_leaf_reset(.path({path, ".child_rst_ni"}), .value(0), .cycles(cycles_to_child_reset));
  endtask : send_unexpected_child_reset

  task send_unexpected_child_release(string path);
    `uvm_info(`gfn, "unexpected child release start", UVM_MEDIUM)
    fork
      set_leaf_reset(.path({path, ".parent_rst_ni"}), .value(0), .cycles(cycles_to_parent_reset));
      set_leaf_reset(.path({path, ".sw_rst_req_i"}), .value(1), .cycles(cycles_to_sw_reset));
      set_leaf_reset(.path({path, ".child_rst_ni"}), .value(0), .cycles(cycles_to_child_reset));
    join

    cfg.scoreboard.set_exp_alert("fatal_cnsty_fault", 1, 20);

    set_leaf_reset(.path({path, ".child_rst_ni"}), .value(1), .cycles(cycles_to_child_release));
  endtask : send_unexpected_child_release

  local task set_leaf_reset(string path, logic value, int cycles);
    cfg.clk_rst_vif.wait_clks(cycles);
    `uvm_info(`gfn, $sformatf("Force %s = %b", path, value), UVM_MEDIUM)
    `DV_CHECK(uvm_hdl_force(path, value))
  endtask : set_leaf_reset

  // Create some unexpected child activity when my_pos is error_pos. The unexpected activity
  // should trigger alerts, so this fails if no alert is generated.
  task unexpected_child_activity(string path);
    int err_value;
    string lpath;
    `DV_SPINWAIT(while (my_pos < error_pos) @cfg.clk_rst_vif.cb;,
                 "Timeout waiting for my_pos < error_pos", 1000_000)

    `DV_SPINWAIT(wait_for_cnsty_idle(path);, "Timeout waiting for cnsty_idle", 1000_000)

    `DV_SPINWAIT(wait_for_alert_sender_ready();, "Timeout waiting for alert_sender ready", 1000_000)
    `DV_CHECK_RANDOMIZE_FATAL(this);
    `uvm_info(`gfn, "Triggering inconsistency", UVM_MEDIUM)
    randcase
      1: send_unexpected_child_reset(path);
      1: send_unexpected_child_release(path);
    endcase

    cfg.clk_rst_vif.wait_clks(cycles_to_check);
    `DV_SPINWAIT(wait(cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.alert_tx_final.alert_p);,
                 "Timeout waiting for alert fatal_cnsty_fault", 10_000)

    lpath = {path, ".child_rst_ni"};
    `DV_CHECK(uvm_hdl_release(lpath))
    lpath = {path, ".parent_rst_ni"};
    `DV_CHECK(uvm_hdl_release(lpath))
    lpath = {path, ".sw_rst_req_i"};
    `DV_CHECK(uvm_hdl_release(lpath))
    // And expect POR bit to be set.
    maybe_por_reset = 1;
    apply_reset();

    // set error_pos to large value
    // after error injection.
    error_pos = 100;
  endtask : unexpected_child_activity

  // wait for parent and child reset deassert.
  // to make sure rstmgr_cnsty_chk state is not Reset state.
  task wait_for_cnsty_idle(string path);
    int value = 1;
    string lpath;

    while (value == 1) begin
      @cfg.clk_rst_vif.cb;
      lpath = {path, ".sync_parent_rst"};
      `DV_CHECK(uvm_hdl_read(lpath, value))
    end
    value = 1;
    while (value == 1) begin
      @cfg.clk_rst_vif.cb;
      lpath = {path, ".sync_child_rst"};
      `DV_CHECK(uvm_hdl_read(lpath, value))
    end
  endtask : wait_for_cnsty_idle

  // This waits until the alert_rx differential pairs are complementary, indicating the
  // end of their initialization phase. This is necessary so the fault injection doesn't
  // happen during initialization, which would end up delaying the outgoing alert.
  task wait_for_alert_sender_ready();
    `uvm_info(`gfn, "Waiting for alert sender ready", UVM_MEDIUM)
    forever @cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.sender_cb begin
      if (cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.sender_cb.alert_rx.ping_p !=
          cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.sender_cb.alert_rx.ping_n &&
          cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.sender_cb.alert_rx.ack_p !=
          cfg.m_alert_agent_cfgs["fatal_cnsty_fault"].vif.sender_cb.alert_rx.ack_n) begin
        `uvm_info(`gfn, "Alert sender is ready", UVM_MEDIUM)
        return;
      end
    end
  endtask : wait_for_alert_sender_ready

  task check_alert_and_cpu_info_after_reset(alert_crashdump_t alert_dump, cpu_crash_dump_t cpu_dump,
                                            logic enable);

    if (error_pos != my_pos) begin
      super.check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, enable);
    end
  endtask : check_alert_and_cpu_info_after_reset

  // Increments my_pos and if it equals error_pos this just waits to give time for the consistency
  // error to be injected and side-effects to be created. Clear the expectation of a por reset
  // since this is a new reset.
  task set_pos_and_wait();
    maybe_por_reset = 0;
    my_pos++;
    `DV_SPINWAIT(while (my_pos == error_pos) @cfg.clk_rst_vif.cb;, $sformatf(
                 "Timeout waiting for my_pos == error_pos ends my_pos:%0d", my_pos), 1000_000)
  endtask : set_pos_and_wait
endclass : rstmgr_leaf_rst_cnsty_vseq
