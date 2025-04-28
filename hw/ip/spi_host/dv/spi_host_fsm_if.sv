// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interface used to have the SPI host FSM decrement the counter by more than 1 unit by
// forcing a decrement in the FSM counter
// This is used currently on tests running VSEQ `spi_host_upper_range_clkdiv_vseq`
// with the purpose of making simulations take less time for longer tests
interface spi_host_fsm_if ();

  // Knowb to be enabled in UVM VSEQs whenever we want the decrement signal to be
  // greater than 1 (currently hardcoded at 16 when in fast_mode)
  bit fast_mode;

  always @(posedge u_fsm.clk_i) begin
    if (u_fsm.rst_ni && fast_mode) begin
      if (!(u_fsm.sw_rst_i || !u_fsm.clk_cntr_en ||
            u_fsm.new_command || u_fsm.is_idle || !u_fsm.clk_cntr_q)) begin
        // This check matches the one defining clk_cntr_d in spi_host_fsm.sv. It expects to
        // decrement by 1. If we are in "fast mode", we should decrement by 16 instead.
        force u_fsm.clk_cntr_d = u_fsm.clk_cntr_q - 16;
        @(posedge u_fsm.clk_i or negedge u_fsm.rst_ni);
        release u_fsm.clk_cntr_d;
      end
    end
  end
endinterface
