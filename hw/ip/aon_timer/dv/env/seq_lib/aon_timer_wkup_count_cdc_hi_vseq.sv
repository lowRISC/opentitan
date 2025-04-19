// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// aon_timer_wkup_count_cdc_hi_vseq aims to get the wkup_count[31:0] to overflow
// in order to have wkup_count[63:32].
// In addition to the lowest 32-bit overflow, the Vseq drives wkup_ctrl.enable via
// the backdoor in order to have finer control as in when the enable sets in due to CDC
// crossing to hit conditional coverage more easily
class aon_timer_wkup_count_cdc_hi_vseq extends aon_timer_smoke_vseq;
    `uvm_object_utils(aon_timer_wkup_count_cdc_hi_vseq)

  localparam int unsigned WKUP_HALF_REG_LP = WKUP_WIDTH/2;
  rand int unsigned delay;

  extern constraint wkup_count_upper_32_bits_c;

  extern function new (string name="");
  // u_wkup_count_hi_cdc CCOV closure task.
  // It's very difficult to close some CCOV for the instance above (including the arbiter)
  // because the counter is 64-bits and is split in two 32-bit half registers which means the
  // 'hi' part of the register won't be counting frequently unless the bottom 32-bits overflow.
  // This task aims to:
  // 1) Disable the wkup_ctrl.enable field at the right time to allow for missing conditional
  //    and branch coverage to be hit in the arbiter (prim_reg_cdc_arb). In particular, the counter
  //    must be disabled exactly at the cycle the 'hi' part of the counter update. This causes
  //    `dst_qs_o != dst_qs_i` which will cause `dst_lat_q=1` and clear all the associated holes.
  // 2) In addition to the above, prim_reg_cdc requires a front-door wkup_count_hi write right after
  //    the counter is disabled in order to achieve the condition `src_update==1 && busy==1`
  //
  // Note: The enabling/disabling as well as some of the write wkup_countr_hi could also be achieved
  //       through front-door accesses. However, it would take longer to close coverage since each
  //       TL access needs to cross the CDC.
  extern task wkup_count_hi_cdc_ccov_closure();
  extern task body();

endclass : aon_timer_wkup_count_cdc_hi_vseq

constraint aon_timer_wkup_count_cdc_hi_vseq::wkup_count_upper_32_bits_c {
  solve delay before wkup_count;
  wkup_thold > 0;
  wkup_count[WKUP_HALF_REG_LP-1:0] == ({WKUP_HALF_REG_LP{1'b1}} - delay);
  delay > 0;
  delay < 15;
}

function aon_timer_wkup_count_cdc_hi_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_wkup_count_cdc_hi_vseq::wkup_count_hi_cdc_ccov_closure();

  // Disable escalation, to allow the wkup_counter to count (aon_timer_core.wkup_incr=1)
  // Otherwise, we probably won't hit the missing coverage holes for wkup_count_hi_cdc and arbiter
  cfg.lc_escalate_en_vif.drive(0);

  for (int i = 0; i < 30; i++) begin
    if (!this.randomize())
      `uvm_fatal(`gfn, "Randomization Failure")

    // Clear interrupts in case any had been raised (via backdoor to avoid any delay)
    csr_utils_pkg::csr_wr(.ptr(ral.intr_state), .value(2'b11), .backdoor(1));
    `uvm_info(`gfn, $sformatf("Initializating AON Timer. Writing 0x%0x to WKUP_COUNT",
                              wkup_count), UVM_DEBUG)
    csr_utils_pkg::csr_wr(.ptr(ral.wkup_count_lo), .value(wkup_count[31:0]), .backdoor(1));
    csr_utils_pkg::csr_wr(.ptr(ral.wkup_count_hi), .value(wkup_count[63:32]), .backdoor(1));
    if (cfg.under_reset) break;

    cfg.aon_clk_rst_vif.wait_clks_or_rst(delay);
    // Enable wkup_counter via backdoor to ensure no CDC delay
    csr_utils_pkg::csr_wr(.ptr(ral.wkup_ctrl.enable), .value(1), .backdoor(1));
    if (cfg.under_reset) break;

    cfg.aon_clk_rst_vif.wait_clks_or_rst(delay+$urandom_range(0,1));

    csr_utils_pkg::csr_wr(.ptr(ral.wkup_ctrl.enable), .value(0), .backdoor(1));
    if (cfg.under_reset) break;

    write_wkup_reg(ral.wkup_count_hi, $random);
    if (cfg.under_reset) break;
    write_wkup_reg(ral.wkup_count_lo, $random);
    if (cfg.under_reset) break;
  end
endtask : wkup_count_hi_cdc_ccov_closure


task aon_timer_wkup_count_cdc_hi_vseq::body();
  wkup_count_hi_cdc_ccov_closure();
endtask : body
