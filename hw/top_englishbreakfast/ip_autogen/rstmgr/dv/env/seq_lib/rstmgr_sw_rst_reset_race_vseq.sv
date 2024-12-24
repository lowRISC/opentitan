// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the software reset functionality: using `sw_rst_regen` and `sw_rst_ctrl_n` CSRs it causes
// resets for each of the bits randomly. It also triggers lc or sys resets to verify the reset
// transitions that cause rising upper resets but non-rising leafs.
//
// Then it clears specific `sw_rst_regwen` bits and attempts to cause resets to determine
// the bits with `sw_rst_regwen` cleared cannot cause a reset.
class rstmgr_sw_rst_reset_race_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_sw_rst_reset_race_vseq)

  `uvm_object_new
  rand int cycles_before_sw_rst;
  rand int cycles_before_reset;

  // When reset is issued the clocks will be stopped, so the sw_rst_ctrl_n writes must
  // start before reset to be safe, or this could wait forever since the clock will stop.
  constraint cycles_racing_c {
    solve cycles_before_reset before cycles_before_sw_rst;
    cycles_before_reset inside {[2 : 8]};
    cycles_before_sw_rst inside {[1 : cycles_before_reset - 1]};
  }

  constraint rstreqs_non_zero_c {rstreqs != '0;}

  task body();
    bit [NumSwResets-1:0] exp_ctrl_n;
    bit [NumSwResets-1:0] sw_rst_regwen = '1;
    int expected;
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
          `uvm_info(`gfn, "Done with sw_rst", UVM_MEDIUM)
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_reset);
          send_hw_reset(rstreqs, .complete_it(0));
          `uvm_info(`gfn, "Done with send_reset", UVM_MEDIUM)
        end
      join
      #(reset_us * 1us);
      reset_done();
      clear_sw_rst_ctrl_n();
      expected = rstreqs << ral.reset_info.hw_req.get_lsb_pos();
      check_reset_info(expected, $sformatf("expected reset_info to match 0x%x", expected));
    end
  endtask
endclass
