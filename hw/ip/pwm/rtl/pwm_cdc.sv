// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: CDC for PWM

module pwm_cdc #(
  parameter int NOutputs = 6
) (
  input                            clk_core_i,
  input                            rst_core_ni,
  input  pwm_reg_pkg::pwm_reg2hw_t reg2hw,
  output pwm_reg_pkg::pwm_reg2hw_t reg2hw_sync,
  output logic                     clr_phase_cntr,
  output logic [NOutputs-1:0]      clr_blink_cntr
);

  wire [31:0] common_sync_in  = {reg2hw.cfg.clk_div.q,
                                 reg2hw.cfg.dc_resn.q,
                                 reg2hw.cfg.cntr_en.q};

  wire [31:0] common_sync_out;
  assign {reg2hw_sync.cfg.clk_div.q,
          reg2hw_sync.cfg.dc_resn.q,
          reg2hw_sync.cfg.cntr_en.q} = common_sync_out;

  // Regen field does not need syncing, but assign it a value for completeness.
  assign reg2hw_sync.regen.q = 1'b0;

  reg [31:0] common_sync_q;

  prim_flop_2sync #(
    .Width(32),
    .ResetValue(32'h0)
  ) u_common_sync1 (
    .clk_i  (clk_core_i),
    .rst_ni (rst_core_ni),
    .d_i    (common_sync_in),
    .q_o    (common_sync_out)
  );

  always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
    if (!rst_core_ni) begin
      common_sync_q <= 32'h0;
    end else begin
      common_sync_q <= common_sync_out;
    end
  end

  // Reset internal counters whenever parameters change. Though this may cause a single clock
  // nondeterministic delay as the buses wind though the CDC, this does not matter, particularly
  // since all channels will experience the same delay.

  assign clr_phase_cntr = (common_sync_q != common_sync_out);

  for (genvar ii = 0; ii < NOutputs; ii++) begin : gen_chan_cdc

    wire [83:0] chan_sync_in  = {reg2hw.pwm_en[ii].q,
                                 reg2hw.invert[ii].q,
                                 reg2hw.pwm_param[ii].phase_delay.q,
                                 reg2hw.pwm_param[ii].htbt_en.q,
                                 reg2hw.pwm_param[ii].blink_en.q,
                                 reg2hw.duty_cycle[ii].a.q,
                                 reg2hw.duty_cycle[ii].b.q,
                                 reg2hw.blink_param[ii].x.q,
                                 reg2hw.blink_param[ii].y.q};

    wire [83:0] chan_sync_out;

    assign {reg2hw_sync.pwm_en[ii].q,
            reg2hw_sync.invert[ii].q,
            reg2hw_sync.pwm_param[ii].phase_delay.q,
            reg2hw_sync.pwm_param[ii].htbt_en.q,
            reg2hw_sync.pwm_param[ii].blink_en.q,
            reg2hw_sync.duty_cycle[ii].a.q,
            reg2hw_sync.duty_cycle[ii].b.q,
            reg2hw_sync.blink_param[ii].x.q,
            reg2hw_sync.blink_param[ii].y.q} = chan_sync_out;

    reg [83:0] chan_sync_q;

    prim_flop_2sync #(
      .Width(84),
      .ResetValue(84'h0)
    ) u_common_sync2 (
      .clk_i  (clk_core_i),
      .rst_ni (rst_core_ni),
      .d_i    (chan_sync_in),
      .q_o    (chan_sync_out)
    );

    always_ff @(posedge clk_core_i or negedge rst_core_ni) begin
      if (!rst_core_ni) begin
        chan_sync_q <= 84'h0;
      end else begin
        chan_sync_q <= chan_sync_out;
      end
    end

    // Though it may be a bit overkill, we reset the internal blink counters whenever any channel
    // specific parameters change.

    assign clr_blink_cntr[ii] = (chan_sync_q != chan_sync_out);

  end : gen_chan_cdc

  // All fields in reg2hw are synced across the CDC except REGEN (the register write enable).
  // Explicitly waive that here.
  logic unused_regen;
  assign unused_regen = reg2hw.regen;

endmodule : pwm_cdc
