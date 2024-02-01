// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// spid_csb_sync detects the deassertion edge (positive edge) of CSB for
// spi_device. With a prim_edge_detector alone, CSB would have pulse width
// requirements relative to clk_i, and these could be restrictive relative to
// the downstream SPI flash.
//
// Instead, use a CSB-clocked toggle and detect the much slower-changing
// toggles, making use of CSB's low duty cycle.
//
// In addition, this module filters CSB "cycles" without SPI clocks.
// The sck_pulse_en_i input allows further filtering of CSB-triggered pulses.
// For example, this can be used to trigger a pulse only when there is a new
// uploaded command.

module spid_csb_sync (
  input clk_i,
  input rst_ni,
  input sck_i,
  input sck_pulse_en_i,
  input csb_i,
  output csb_deasserted_pulse_o
);

  logic sck_toggle, csb_toggle, sys_toggle, sys_toggle_last;

  // CSB and SCK have setup / hold relationships for SPI flash devices. Only
  // change counts on CSB posedge if there is at least one SCK cycle.
  always_ff @(posedge sck_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sck_toggle <= 1'b0;
    end else begin
      if (sck_pulse_en_i) begin
        sck_toggle <= ~csb_toggle;
      end
    end
  end

  // Signal CSB de-assertion with a change in count, but only do it if the
  // change originated from the SCK domain.
  always_ff @(posedge csb_i or negedge rst_ni) begin
    if (!rst_ni) begin
      csb_toggle <= 1'b0;
    end else begin
      csb_toggle <= sck_toggle;
    end
  end

  // clk_i is asynchronous to CSB/SCK, so use a synchronizer.
  prim_flop_2sync #(
    .Width     (1)
  ) u_count_sync (
    .clk_i,
    .rst_ni,
    .d_i       (csb_toggle),
    .q_o       (sys_toggle)
  );

  // sys_toggle_last is used to generate the pulse on differences.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sys_toggle_last <= 1'b0;
    end else begin
      sys_toggle_last <= sys_toggle;
    end
  end

  assign csb_deasserted_pulse_o = (sys_toggle != sys_toggle_last);
endmodule : spid_csb_sync
