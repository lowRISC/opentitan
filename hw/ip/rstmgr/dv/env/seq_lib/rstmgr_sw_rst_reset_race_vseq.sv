// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the software reset functionality: using `sw_rst_regen` and `sw_rst_ctrl_n` CSRs it causes
// resets for each of the bits randomly. It also triggers lc or sys resets to verify the reset
// transitions that cause rising upper resets but non-rising leafs.
//
// Then it clears specific `sw_rst_regen` bits and attempts to cause resets to determine
// the bits with `sw_rst_regwen` cleared cannot cause a reset.
class rstmgr_sw_rst_reset_race_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_sw_rst_reset_race_vseq)

  `uvm_object_new
  rand int cycles_before_sw_rst;
  rand int cycles_before_reset;
  constraint cycles_racing_c {
    cycles_before_sw_rst inside {[2 : 8]};
    cycles_before_reset inside {[2 : 8]};
  }

  constraint rstreqs_non_zero_c {rstreqs != '0;}

  task body();
    bit [NumSwResets-1:0] exp_ctrl_n;
    bit [NumSwResets-1:0] sw_rst_regwen = '1;
    alert_pkg::alert_crashdump_t bogus_alert_dump = '1;
    rv_core_ibex_pkg::cpu_crash_dump_t bogus_cpu_dump = '1;
    set_alert_and_cpu_info_for_capture(bogus_alert_dump, bogus_cpu_dump);

    for (int i = 0; i < num_trans; ++i) begin
      csr_wr(.ptr(ral.reset_info), .value('1));

      `DV_CHECK_RANDOMIZE_FATAL(this)
      fork
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_sw_rst);
          check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regwen, 0);
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_reset);
          send_reset(.reset_cause(pwrmgr_pkg::HwReq), .rstreqs(rstreqs), .clear_it(0));
        end
      join
      cfg.clk_rst_vif.wait_clks(20);
      release_reset(pwrmgr_pkg::HwReq);
      clear_sw_rst_ctrl_n();
      check_reset_info({rstreqs, 4'h0}, $sformatf(
                       "expected reset_info to match 0x%x", {rstreqs, 4'h0}));
    end
  endtask
endclass
