// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This VSEQ configures the timers and enables them long enough so the time the counter is disabled
// is close to the boundary count > threshold.
// In addition, after the counters are disabled, the VSEQ reads the interrupt state and clears the
// set bits like SW would do.
// For extra stimulus, there's a random process injecting random intr_test writes
class aon_timer_alternating_enable_on_off_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_alternating_enable_on_off_vseq)

  // Don't lock WDOG configuration, so we can reconfigure in the ON/OFF alternating stimulus
  extern constraint wdog_regwen_c;

  extern function new (string name="");

  // This task enables the counter, and waits for a number of AON cycles close to the boundary
  // where the counter exceeds the threshold, then disables the counter via the backdoor.
  extern task alternate_on_off(bit wkup, int unsigned delay);
  extern task read_intr_and_clear();

  extern task body();
endclass : aon_timer_alternating_enable_on_off_vseq

constraint aon_timer_alternating_enable_on_off_vseq::wdog_regwen_c{
  wdog_regwen == 1;
}

function aon_timer_alternating_enable_on_off_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_alternating_enable_on_off_vseq::alternate_on_off(bit wkup, int unsigned delay);
  int unsigned min_delay = (delay <= 2) ? delay : delay - 2;
  `uvm_info(`gfn, $sformatf("Enabling %0s counter", wkup ? "WKUP" : "WDOG"), UVM_DEBUG)
  write_wkup_reg(wkup ? ral.wkup_ctrl.enable : ral.wdog_ctrl.enable, 1);
  cfg.aon_clk_rst_vif.wait_clks_or_rst($urandom_range(min_delay, delay+2));
  // Disable via the backdoor to have counter disable with immediate effect after delay
  `uvm_info(`gfn, $sformatf("Disabling %0s counter", wkup ? "WKUP" : "WDOG"), UVM_DEBUG)
  csr_utils_pkg::csr_wr(.ptr(wkup ? ral.wkup_ctrl.enable : ral.wdog_ctrl.enable), .value(0),
                        .backdoor(1));
endtask

task aon_timer_alternating_enable_on_off_vseq::read_intr_and_clear();
  bit [1:0] intr_state_value;
  // Give some delay for interrupts to propagate
  cfg.aon_clk_rst_vif.wait_clks_or_rst($urandom_range(10, 15));
  if (cfg.under_reset) return;
  wait (ral.intr_state.m_is_busy == 0);
  csr_utils_pkg::csr_rd(ral.intr_state, intr_state_value);
  cfg.clk_rst_vif.wait_clks_or_rst($urandom_range(1, 15));
  if (cfg.under_reset) return;
  wait (ral.intr_state.m_is_busy == 0);
  csr_utils_pkg::csr_wr(ral.intr_state, intr_state_value);
  cfg.clk_rst_vif.wait_clks_or_rst($urandom_range(5, 50));
endtask

task aon_timer_alternating_enable_on_off_vseq::body();
  bit counter_stim_done;

  // Disabling escalation otherwise TB won't generate interrupts
  cfg.lc_escalate_en_vif.drive(0);
  fork : iso_fork
    fork
      begin : main_stim
        for (int i = 0; i < 20; i++) begin
          // Configure WDOG/WKUP regs in parallel
          fork : counter_init
            wkup_init();
            wdog_init();
          join : counter_init
          if (cfg.under_reset) break;
          fork : alternate_enable
            // Enable / disable each counter thread in parallel
            alternate_on_off(.wkup(1), .delay(wkup_count_gap));
            alternate_on_off(.wkup(0), .delay(wdog_count_gap));
          join  : alternate_enable
          if (cfg.under_reset) break;
          // read intr_state in case there are interrupts and clear them:
          read_intr_and_clear();
          if (cfg.under_reset) break;
          if (!this.randomize())
            `uvm_fatal(`gfn, "Randomization Failure")
        end
        counter_stim_done = 1;
      end : main_stim
      begin : random_test_intr_stim
        // Randomly write intr_state/test
        while (counter_stim_done==0) begin
          csr_utils_pkg::csr_wr(ral.intr_test, $random);
          if (cfg.under_reset || counter_stim_done)
            break;
          cfg.clk_rst_vif.wait_clks_or_rst($urandom_range(5, 50));
        end
      end : random_test_intr_stim
    join
    disable fork;
  join : iso_fork

endtask : body
