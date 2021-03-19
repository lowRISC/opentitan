// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module pinmux_wkup import pinmux_pkg::*; import pinmux_reg_pkg::*; #(
  parameter int Cycles = 4
) (
  input                    clk_i,
  input                    rst_ni,
  // Always on clock / reset
  input                    clk_aon_i,
  input                    rst_aon_ni,
  // These signals get synchronized to the
  // slow AON clock within this module.
  // Note that wkup_en_i is assumed to be level encoded.
  input                    wkup_en_i,
  input                    filter_en_i,
  input wkup_mode_e        wkup_mode_i,
  input [WkupCntWidth-1:0] wkup_cnt_th_i,
  input                    pin_value_i,
  // Signals to/from cause register.
  // They are synched to/from the AON clock internally
  input                    wkup_cause_valid_i,
  input                    wkup_cause_data_i,
  output                   wkup_cause_data_o,
  // This signal is running on the AON clock
  // and is held high as long as the cause register
  // has not been cleared.
  output logic             aon_wkup_req_o
);

  ///////////////////////////
  // Input Synchronization //
  ///////////////////////////

  // Synchronize configuration to slow clock
  wkup_mode_e aon_wkup_mode_q;
  logic aon_filter_en_q;
  logic aon_wkup_en_d, aon_wkup_en_q;
  logic [WkupCntWidth-1:0] aon_wkup_cnt_th_q;

  prim_flop_2sync #(
    .Width(1)
  ) i_prim_flop_2sync_config (
    .clk_i  ( clk_aon_i      ),
    .rst_ni ( rst_aon_ni     ),
    .d_i    ( wkup_en_i     ),
    .q_o    ( aon_wkup_en_d )
  );

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : p_sync
    if (!rst_aon_ni) begin
      aon_wkup_en_q     <= 1'b0;
      aon_wkup_mode_q   <= Posedge;
      aon_filter_en_q   <= 1'b0;
      aon_wkup_cnt_th_q <= '0;
    end else begin
      aon_wkup_en_q <= aon_wkup_en_d;
      // latch these when going into sleep. note that these
      // config signals should be stable at this point, since
      // SW has configured them many cycles ago. hence no
      // explicit multibit consistency check is performed.
      if (aon_wkup_en_d & !aon_wkup_en_q) begin
        aon_wkup_mode_q   <= wkup_mode_i;
        aon_filter_en_q   <= filter_en_i;
        aon_wkup_cnt_th_q <= wkup_cnt_th_i;
      end
    end
  end

  ////////////////////////////
  // Optional Signal Filter //
  ////////////////////////////

  // This uses a lower value for filtering than GPIO since
  // the always-on clock is slower. This can be disabled,
  // in which case the signal is just combinationally bypassed.
  logic aon_filter_out, aon_filter_out_d, aon_filter_out_q;
  prim_filter #(
    .Cycles(Cycles)
  ) i_prim_filter (
    .clk_i    ( clk_aon_i       ),
    .rst_ni   ( rst_aon_ni      ),
    .enable_i ( aon_filter_en_q ),
    .filter_i ( pin_value_i     ),
    .filter_o ( aon_filter_out  )
  );

  // Run this through a 2 stage synchronizer to
  // prevent metastability.
  prim_flop_2sync #(
    .Width(1)
  ) i_prim_flop_2sync_filter (
    .clk_i  ( clk_aon_i  ),
    .rst_ni ( rst_aon_ni ),
    .d_i    ( aon_filter_out ),
    .q_o    ( aon_filter_out_d )
  );

  //////////////////////
  // Pattern Matching //
  //////////////////////

  logic aon_rising, aon_falling;
  assign aon_falling = ~aon_filter_out_d &  aon_filter_out_q;
  assign aon_rising  =  aon_filter_out_d & ~aon_filter_out_q;

  logic aon_cnt_en, aon_cnt_eq_th;
  logic [WkupCntWidth-1:0] aon_cnt_d, aon_cnt_q;
  assign aon_cnt_d = (aon_cnt_eq_th) ? '0                :
                     (aon_cnt_en)    ?  aon_cnt_q + 1'b1 : '0;

  assign aon_cnt_eq_th = aon_cnt_q == aon_wkup_cnt_th_q;

  logic aon_wkup_pulse;
  always_comb begin : p_mode
    aon_wkup_pulse = 1'b0;
    aon_cnt_en     = 1'b0;
    if (aon_wkup_en_q) begin
      unique case (aon_wkup_mode_q)
        Negedge:   aon_wkup_pulse = aon_falling;
        Edge:      aon_wkup_pulse = aon_rising | aon_falling;
        HighTimed: begin
          aon_cnt_en = aon_filter_out_d;
          aon_wkup_pulse = aon_cnt_eq_th;
        end
        LowTimed: begin
          aon_cnt_en = ~aon_filter_out_d;
          aon_wkup_pulse = aon_cnt_eq_th;
        end
        // Default to rising
        default:   aon_wkup_pulse = aon_rising;
      endcase
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : p_aon_pattern
    if (!rst_aon_ni) begin
      aon_filter_out_q <= 1'b0;
      aon_cnt_q        <= '0;
    end else begin
      aon_filter_out_q <= aon_filter_out_d;
      aon_cnt_q        <= aon_cnt_d;
    end
  end

  ////////////////////
  // Cause register //
  ////////////////////

  // to AON domain
  logic aon_wkup_cause_valid, aon_wkup_cause_data;
  logic aon_wkup_cause_d, aon_wkup_cause_q;

  prim_flop_2sync #(
    .Width(1)
  ) i_prim_flop_2sync_cause_in (
    .clk_i  ( clk_aon_i  ),
    .rst_ni ( rst_aon_ni ),
    .d_i    ( wkup_cause_data_i   ),
    .q_o    ( aon_wkup_cause_data )
  );

  prim_pulse_sync i_prim_pulse_sync_cause (
    .clk_src_i   ( clk_i                ),
    .rst_src_ni  ( rst_ni               ),
    .src_pulse_i ( wkup_cause_valid_i   ),
    .clk_dst_i   ( clk_aon_i            ),
    .rst_dst_ni  ( rst_aon_ni           ),
    .dst_pulse_o ( aon_wkup_cause_valid )
  );

  // note that aon_wkup_pulse will not be asserted when not in sleep mode
  assign aon_wkup_cause_d = (aon_wkup_cause_valid) ? aon_wkup_cause_q & aon_wkup_cause_data :
                                                     aon_wkup_cause_q | aon_wkup_pulse;

  // output to power manager
  assign aon_wkup_req_o = aon_wkup_cause_q;

  // output to CSR
  prim_flop_2sync #(
    .Width(1)
  ) i_prim_flop_2sync_cause_out (
    .clk_i,
    .rst_ni,
    .d_i    ( aon_wkup_cause_q  ),
    .q_o    ( wkup_cause_data_o )
  );

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin : p_aon_cause
    if (!rst_aon_ni) begin
      aon_wkup_cause_q <= 1'b0;
    end else begin
      aon_wkup_cause_q <= aon_wkup_cause_d;
    end
  end

endmodule : pinmux_wkup
