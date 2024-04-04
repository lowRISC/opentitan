// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the POR stretching functionality: it directly controls the por_n_i input at the start of
// the test, and randomly glitches it for a few cycles at intervals less than the stretch cycle
// count, which is at least 32 cycles, to make sure the internal and output resets won't be
// released until the input is held steady for a sufficient number of cycles.
class rstmgr_por_stretcher_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_por_stretcher_vseq)

  `uvm_object_new

  // Wait a few cycles for resets to propagate before we start flipping por_n_i, to avoid
  // spurious SVA failures dut to missing rise transitions of leaf resets.
  localparam int AON_CYCLES_BEFORE_START = 4;

  // Wait this many cycles before checking for side effects of a complete reset.
  localparam int AON_CYCLES_BEFORE_RESET_CHECK = 45;

  rand int glitch_separation_cycles;
  rand int glitch_duration_cycles;

  // The separation between glitches that will cause a reset to fail to propagate.
  constraint glitch_separation_cycles_c {glitch_separation_cycles inside {[1 : 35]};}
  // The duration cycle is not very interesting.
  constraint glitch_duration_cycles_c {glitch_duration_cycles inside {[1 : 8]};}

  task body();
    cfg.aon_clk_rst_vif.wait_clks(AON_CYCLES_BEFORE_START);
    for (int i = 0; i < num_trans; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.rstmgr_vif.por_n = 1'b1;
      cfg.aon_clk_rst_vif.wait_clks(glitch_separation_cycles);
      cfg.rstmgr_vif.por_n = 1'b0;
      cfg.aon_clk_rst_vif.wait_clks(glitch_duration_cycles);
      `DV_CHECK_EQ(cfg.rstmgr_vif.resets_o.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel], 1'b0)
    end
    por_reset_done(.complete_it(1));
    csr_rd_check(.ptr(ral.reset_info.por), .compare_value(1'b1),
                 .err_msg("Unexpected reset_info.por low"));
  endtask
endclass
