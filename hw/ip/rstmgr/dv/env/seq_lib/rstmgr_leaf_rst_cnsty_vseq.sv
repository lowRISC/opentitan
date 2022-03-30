// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// Test creates a set of reset event - low power, hw req, ndm and sw -.
// my_pos indicates the begining of each reset event.
// 1 - lowpwer reset
// 2 - hw req reset
// 3 - ndm reset
// 4 - sw reset
// LIST_OF_LEAFS has the name of all leaf reset modules.
// At each round, error_pos is assigned to random value [1:4].
// when error_pos = my_pos, reset consistency error is created to the current
// leaf module and test waits for alert_fatal_cnsty_fault.
// Upon detecting the alert, dut reset is applied then move to the next
// leaf module.
class rstmgr_leaf_rst_cnsty_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_leaf_rst_cnsty_vseq)

  `uvm_object_new

  string leaf_path;
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


  task body();
    for (int i = 0; i < LIST_OF_LEAFS.size(); ++i) begin
      leaf_path = {"tb.dut.", LIST_OF_LEAFS[i], ".gen_rst_chk.u_rst_chk"};
      error_pos = $urandom_range(1, 4);
      my_pos = 0;
      `uvm_info(`gfn, $sformatf("Round %0d %s  pos:%0d", i, leaf_path, error_pos), UVM_MEDIUM)

      fork
        unexpected_child_activity(leaf_path);
        begin
          set_pos_and_wait();
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);
          csr_wr(.ptr(ral.reset_info), .value('1));
          // Send low power entry reset.
          send_reset(pwrmgr_pkg::LowPwrEntry, '0);
          check_reset_info(2, "expected reset_info to indicate low power");
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

          csr_wr(.ptr(ral.reset_info), .value('1));
          cfg.io_div4_clk_rst_vif.wait_clks(10);

          // Send HwReq.
          // Enable alert_info and cpu_info capture.
          set_pos_and_wait();
          `DV_CHECK_RANDOMIZE_FATAL(this)
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);
          send_reset(pwrmgr_pkg::HwReq, rstreqs);
          check_reset_info({rstreqs, 4'h0},
                           $sformatf("expected reset_info to match 0x%x", {rstreqs, 4'h0}));
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b0);

          csr_wr(.ptr(ral.reset_info), .value('1));

          set_pos_and_wait();
          `DV_CHECK_RANDOMIZE_FATAL(this)
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

          // Send debug reset.
          send_ndm_reset();
          check_reset_info(4, "Expected reset_info to indicate ndm reset");
          check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, 1'b1);

          csr_wr(.ptr(ral.reset_info), .value('1));

          set_pos_and_wait();
          `DV_CHECK_RANDOMIZE_FATAL(this)
          set_alert_and_cpu_info_for_capture(alert_dump, cpu_dump);

          // Send sw reset.
          send_sw_reset(MuBi4True);
          check_reset_info(8, "Expected reset_info to indicate sw reset");
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

    // assert child reset
    set_leaf_reset(.path({path, ".child_rst_ni"}), .value(0), .cycles(cycles_to_child_reset));
  endtask // send_unexpected_child_reset

  task send_unexpected_child_release(string path);
    `uvm_info(`gfn, "unexpected child release start", UVM_MEDIUM)
    fork
      set_leaf_reset(.path({path, ".parent_rst_ni"}), .value(0), .cycles(cycles_to_parent_reset));
      set_leaf_reset(.path({path, ".sw_rst_req_i"}), .value(1), .cycles(cycles_to_sw_reset));
      set_leaf_reset(.path({path, ".child_rst_ni"}), .value(0), .cycles(cycles_to_child_reset));
    join
    set_leaf_reset(.path({path, ".child_rst_ni"}), .value(1), .cycles(cycles_to_child_release));
  endtask // send_unexpected_child_release

  local task set_leaf_reset(string path, logic value, int cycles);
    cfg.clk_rst_vif.wait_clks(cycles);
    `uvm_info(`gfn, $sformatf("Force %s = %b", path, value), UVM_MEDIUM)
    `DV_CHECK(uvm_hdl_force(path, value))
  endtask // set_leaf_reset

  task unexpected_child_activity(string path);
    int err_value;
    string lpath;
    `DV_SPINWAIT(
        while (my_pos < error_pos) @cfg.clk_rst_vif.cb;,
        "Timeout waiting for my_pos < error_pos",
        1000_000)

    `DV_SPINWAIT(
        wait_for_cnsty_idle(path);,
        "Timeout waiting for cnsty_idle",
        1000_000)

    `DV_CHECK_RANDOMIZE_FATAL(this);
    randcase
      1: send_unexpected_child_reset(path);
      1: send_unexpected_child_release(path);
    endcase // randcase

    cfg.clk_rst_vif.wait_clks(cycles_to_check);

    `DV_SPINWAIT(
        wait(cfg.m_alert_agent_cfg["fatal_cnsty_fault"].vif.alert_tx_final.alert_p);,
        "Timeout waiting for alert fatal_cnsty_fault",
        10_000)

    lpath = {path, ".child_rst_ni"};
    `DV_CHECK(uvm_hdl_release(lpath))
    lpath = {path, ".parent_rst_ni"};
    `DV_CHECK(uvm_hdl_release(lpath))
    lpath = {path, ".sw_rst_req_i"};
    `DV_CHECK(uvm_hdl_release(lpath))
    apply_reset();

    // set error_pos to large value
    // after error injection.
    error_pos = 100;
  endtask // unexpected_child_activity

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
  endtask // wait_for_cnsty_idle

  task check_alert_and_cpu_info_after_reset(
    alert_crashdump_t alert_dump, cpu_crash_dump_t cpu_dump, logic enable);

    if (error_pos != my_pos) begin
      super.check_alert_and_cpu_info_after_reset(alert_dump, cpu_dump, enable);
    end
  endtask // check_alert_and_cpu_info_after_reset

  task set_pos_and_wait();
    my_pos++;
    `DV_SPINWAIT(
        while (my_pos == error_pos) @cfg.clk_rst_vif.cb;,
        $sformatf("Timeout waiting for my_pos == error_pos ends my_pos:%0d",my_pos),
        1000_000)
  endtask // set_pos_and_wait
endclass // rstmgr_leaf_rst_cnsty_vseq
