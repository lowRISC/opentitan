// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_base_vseq extends cip_base_vseq #(
    .RAL_T               (aon_timer_reg_block),
    .CFG_T               (aon_timer_env_cfg),
    .COV_T               (aon_timer_env_cov),
    .VIRTUAL_SEQUENCER_T (aon_timer_virtual_sequencer)
  );
  `uvm_object_utils(aon_timer_base_vseq)

  // If this is set, the AON clock starts first and then the fast clock starts sometime later. If
  // not, they start in parallel. Since the fast clock is *much* quicker, the practical result is
  // that it starts first.
  // Currently set to 1 always so AON clock always start first. The testbench doesn't correctly
  // support AON and fast clock starting together. Within OpenTitan earlgrey the aon clock is always
  // active before the fast path so the reset_aon_first == 0 mode isn't required. Leaving the
  // functionality in for now whilst we decide if we want to support reset_aon_first == 0 in the
  // testbench or remove this functionality entirely.
  // rand bit reset_aon_first;
  bit reset_aon_first = 1;

  // Should the escalation signal be enabled at the start of time?
  rand bit initial_lc_escalate_en;

  // When this is not set, we are locking the configuration registers of watchdog timer after its
  // initial setup.
  rand bit wdog_regwen;

  // Is the chip in sleep at the start of time? In the real chip, the answer is (obviously) no, but
  // the design should work either way so we may as well test it.
  rand bit initial_sleep_mode;

  // Randomize Bark/Bite and Wake-up thresholds for the counter
  rand bit [63:0] wkup_thold;
  rand bit [31:0] wdog_bark_thold;
  rand bit [31:0] wdog_bite_thold;

  // Randomize Bark/Bite and Wake-up thresholds for the counter
  rand bit [63:0] wkup_count;
  rand bit [31:0] wdog_count;

  // Used to determine the differenceto initialise the counts with respect to the thresholds
  rand int unsigned wkup_count_gap, wdog_count_gap;
  // When set randomisation tries to set the count and threshold so that the bite is likely hit:
  rand bit          aim_bite;

  // Used to randomly configure wdog_ctrl.pause_in_sleep
  rand bit          wdog_ctrl_pause_in_sleep;

  // Limits threshold and count values
  extern constraint thold_count_c;

  extern function new (string name="");
  extern virtual task dut_init(string reset_kind = "HARD");
  extern virtual task aon_timer_shutdown();
  extern task aon_timer_init();
  extern virtual task apply_reset(string kind = "HARD");
  extern virtual task apply_resets_concurrently(int reset_duration_ps = 0);
  extern task wait_for_interrupt(bit intr_state_read = 1);

endclass : aon_timer_base_vseq

constraint aon_timer_base_vseq::thold_count_c {
  solve wkup_count_gap, wkup_thold before wkup_count;
  solve aim_bite, wdog_count_gap, wdog_bark_thold, wdog_bite_thold before wdog_count;
  wkup_count_gap inside {[1:500]};
  wdog_count_gap inside {[1:500]};

  wkup_thold      inside {[1:10]};
  wdog_bark_thold inside {[1:10]};
  wdog_bite_thold inside {[1:10]};

  wkup_thold      <= (2**64-1);
  wdog_bark_thold <= (2**32-1);
  wdog_bite_thold <= (2**32-1);

  wkup_count inside {[wkup_thold-wkup_count_gap:wkup_thold]};
  !aim_bite -> wdog_count inside {[wdog_bark_thold-wdog_count_gap:wdog_bark_thold]};
  aim_bite  -> wdog_count inside {[wdog_bite_thold-wdog_count_gap:wdog_bite_thold]};

}

function aon_timer_base_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init();

  // Don't use generic interrupt clear as timer interrupts can sometimes trigger between clearing
  // them and checking they're zero.
  do_clear_all_interrupts = 1'b0;
endtask : dut_init

task aon_timer_base_vseq::aon_timer_shutdown();
  `uvm_info(`gfn, "Shutting down AON Timer...", UVM_LOW)

  `uvm_info(`gfn, "Writing 0 to WKUP_CTRL and WDOG_CTRL to disable AON timer", UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b0);
  csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, 1'b0);

  `uvm_info(`gfn, "Clearing interrupts, count registers and wakeup request.", UVM_HIGH)
  // Clear wake-up request if we have any
  csr_utils_pkg::csr_wr(ral.wkup_cause, 1'b0);

  // Clear the interrupts
  csr_utils_pkg::csr_wr(ral.intr_state, 2'b11);

  `uvm_info(`gfn, $sformatf({"Initializating AON Timer. Writing ",
                             "0x%0x to WKUP_COUNT and 0x%0x ",
                             "to WDOG_COUNT."},
                            wkup_count, wdog_count), UVM_LOW)
  // Register Write
  csr_utils_pkg::csr_wr(ral.wkup_count_lo, wkup_count[31:0]);
  csr_utils_pkg::csr_wr(ral.wkup_count_hi, wkup_count[63:32]);
  csr_utils_pkg::csr_wr(ral.wdog_count, wdog_count);

  // Wait to settle registers on AON timer domain
  cfg.aon_clk_rst_vif.wait_clks(5);
endtask : aon_timer_shutdown

// setup basic aon_timer features
task aon_timer_base_vseq::aon_timer_init();

  // Clear the interrupts
  csr_utils_pkg::csr_wr(ral.intr_state, 2'b11);

  `uvm_info(`gfn, "Initializating AON Timer. Writing 0 to WKUP_COUNT and WDOG_COUNT", UVM_LOW)
  // Register Write
  csr_utils_pkg::csr_wr(ral.wkup_count_lo, 32'h0000_0000);
  csr_utils_pkg::csr_wr(ral.wkup_count_hi, 32'h0000_0000);
  csr_utils_pkg::csr_wr(ral.wdog_count, 32'h0000_0000);

  `uvm_info(`gfn, "Randomizing AON Timer thresholds", UVM_HIGH)

  `uvm_info(`gfn, $sformatf("Writing 0x%0h to wkup_thold", wkup_thold), UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wkup_thold_lo, wkup_thold[31:0]);
  csr_utils_pkg::csr_wr(ral.wkup_thold_hi, wkup_thold[63:32]);

  `uvm_info(`gfn, $sformatf("Writing 0x%0h to wdog_bark_thold", wdog_bark_thold), UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wdog_bark_thold, wdog_bark_thold);

  `uvm_info(`gfn, $sformatf("Writing 0x%0h to wdog_bite_thold", wdog_bite_thold), UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wdog_bite_thold, wdog_bite_thold);

  cfg.lc_escalate_en_vif.drive(0);

  `uvm_info(`gfn, $sformatf("Writing 0x%0h to WDOG_REGWEN", wdog_regwen), UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wdog_regwen, wdog_regwen);

endtask : aon_timer_init

task aon_timer_base_vseq::apply_reset(string kind = "HARD");
  cfg.lc_escalate_en_vif.drive(initial_lc_escalate_en);
  cfg.sleep_vif.drive(initial_sleep_mode);

  // Bring up the clocks in either order. We can't just race them by running them in parallel,
  // because the AON clock is much slower so will always come up second.
  // This gives aon_rst a value first before following the normal routine.
  // We cannot completely serialize the resets as that would break device assumptions
  // on CDC paths were both sides are always reset together.
  if (kind == "HARD" && reset_aon_first) begin
    cfg.aon_clk_rst_vif.drive_rst_pin(.val('0));
    #1ps;
  end

  fork
    if (kind == "HARD") cfg.aon_clk_rst_vif.apply_reset();
    super.apply_reset(kind);
  join

endtask : apply_reset

task aon_timer_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.aon_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.aon_clk_rst_vif.clk_period_ps);
  cfg.aon_clk_rst_vif.drive_rst_pin(1);
endtask : apply_resets_concurrently

task aon_timer_base_vseq::wait_for_interrupt(bit intr_state_read = 1);
  if (cfg.aon_clk_rst_vif.rst_n && !cfg.aon_intr_vif.pins) begin
    uvm_reg_data_t intr_state_value;

    @(negedge cfg.aon_clk_rst_vif.rst_n or cfg.aon_intr_vif.pins);

    if (intr_state_read) begin
      // Wait 2 clocks to ensure interrupt is visible on intr_state read
      cfg.aon_clk_rst_vif.wait_clks(2);
      csr_utils_pkg::csr_rd(ral.intr_state, intr_state_value);
    end

    // If we are getting an interrupt, let's asssume sleep signal immediately goes low.
    if (cfg.aon_intr_vif.pins) begin
      cfg.sleep_vif.drive(0);
    end
  end
endtask : wait_for_interrupt
