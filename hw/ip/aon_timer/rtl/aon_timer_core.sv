// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module aon_timer_core (
  input  logic                      clk_aon_i,
  input  logic                      rst_aon_ni,

  input  lc_ctrl_pkg::lc_tx_t [2:0] lc_cpu_en_i,
  input  logic                      sleep_mode_i,

  // Register read outputs
  output logic                      wkup_enable_o,
  output logic [11:0]               wkup_prescaler_o,
  output logic [31:0]               wkup_thold_o,
  output logic [31:0]               wkup_count_o,
  output logic                      wdog_enable_o,
  output logic                      wdog_pause_o,
  output logic [31:0]               wdog_bark_thold_o,
  output logic [31:0]               wdog_bite_thold_o,
  output logic [31:0]               wdog_count_o,

  // Register write inputs
  input  logic                      wkup_ctrl_reg_wr_i,
  input  logic [12:0]               wkup_ctrl_wr_data_i,
  input  logic                      wkup_thold_reg_wr_i,
  input  logic [31:0]               wkup_thold_wr_data_i,
  input  logic                      wkup_count_reg_wr_i,
  input  logic [31:0]               wkup_count_wr_data_i,
  input  logic                      wdog_ctrl_reg_wr_i,
  input  logic [1:0]                wdog_ctrl_wr_data_i,
  input  logic                      wdog_bark_thold_reg_wr_i,
  input  logic [31:0]               wdog_bark_thold_wr_data_i,
  input  logic                      wdog_bite_thold_reg_wr_i,
  input  logic [31:0]               wdog_bite_thold_wr_data_i,
  input  logic                      wdog_count_reg_wr_i,
  input  logic [31:0]               wdog_count_wr_data_i,

  output logic                      wkup_intr_o,
  output logic                      wdog_intr_o,
  output logic                      wdog_reset_req_o
);

  // Wakeup signals
  logic        wkup_enable_d, wkup_enable_q;
  logic [11:0] wkup_prescaler_d, wkup_prescaler_q;
  logic [31:0] wkup_thold_d, wkup_thold_q;
  logic [11:0] prescale_count_d, prescale_count_q;
  logic        prescale_en;
  logic        wkup_incr, wkup_count_en;
  logic [31:0] wkup_count_d, wkup_count_q;
  // Watchdog signals
  logic        wdog_enable_d, wdog_enable_q;
  logic        wdog_pause_d, wdog_pause_q;
  logic [31:0] wdog_bark_thold_d, wdog_bark_thold_q;
  logic [31:0] wdog_bite_thold_d, wdog_bite_thold_q;
  logic        wdog_incr, wdog_count_en;
  logic [31:0] wdog_count_d, wdog_count_q;

  //////////////////
  // Wakeup Timer //
  //////////////////

  // Wakeup control register
  assign wkup_prescaler_d = wkup_ctrl_wr_data_i[12:1];
  assign wkup_enable_d    = wkup_ctrl_wr_data_i[0];

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wkup_prescaler_q <= 12'h000;
      wkup_enable_q    <= 1'b0;
    end else if (wkup_ctrl_reg_wr_i) begin
      wkup_prescaler_q <= wkup_prescaler_d;
      wkup_enable_q    <= wkup_enable_d;
    end
  end

  assign wkup_enable_o    = wkup_enable_q;
  assign wkup_prescaler_o = wkup_prescaler_q;

  // Wakeup threshold register
  assign wkup_thold_d = wkup_thold_wr_data_i;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wkup_thold_q <= 32'd0;
    end else if (wkup_thold_reg_wr_i) begin
      wkup_thold_q <= wkup_thold_d;
    end
  end

  assign wkup_thold_o = wkup_thold_q;

  // Prescaler counter
  assign prescale_count_d = wkup_incr ? 12'h000 : (prescale_count_q + 12'h001);
  assign prescale_en      = lc_cpu_en_i[0] == lc_ctrl_pkg::Off;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      prescale_count_q <= 12'h000;
    end else if (prescale_en) begin
      prescale_count_q <= prescale_count_d;
    end
  end

  // Wakeup timer count
  assign wkup_incr     = (lc_cpu_en_i[1] == lc_ctrl_pkg::Off) & wkup_enable_q &
                         (prescale_count_q == wkup_prescaler_q);
  assign wkup_count_d  = wkup_count_reg_wr_i ? wkup_count_wr_data_i :
                                               (wkup_count_q + 32'd1);
  assign wkup_count_en = wkup_incr | wkup_count_reg_wr_i;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wkup_count_q <= 32'd0;
    end else if (wkup_count_en) begin
      wkup_count_q <= wkup_count_d;
    end
  end

  assign wkup_count_o = wkup_count_q;

  // Timer interrupt
  assign wkup_intr_o = wkup_incr & (wkup_count_q == wkup_thold_q);

  ////////////////////
  // Watchdog Timer //
  ////////////////////

  // Watchdog control register
  assign wdog_pause_d  = wdog_ctrl_wr_data_i[1];
  assign wdog_enable_d = wdog_ctrl_wr_data_i[0];

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wdog_pause_q  <= 1'b0;
      wdog_enable_q <= 1'b0;
    end else if (wdog_ctrl_reg_wr_i) begin
      wdog_pause_q  <= wdog_pause_d;
      wdog_enable_q <= wdog_enable_d;
    end
  end

  assign wdog_enable_o = wdog_enable_q;
  assign wdog_pause_o  = wdog_pause_q;

  // Watchdog bark threshold register
  assign wdog_bark_thold_d = wdog_bark_thold_wr_data_i;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wdog_bark_thold_q <= 32'd0;
    end else if (wdog_bark_thold_reg_wr_i) begin
      wdog_bark_thold_q <= wdog_bark_thold_d;
    end
  end

  assign wdog_bark_thold_o = wdog_bark_thold_q;

  // Watchdog bite threshold register
  assign wdog_bite_thold_d = wdog_bite_thold_wr_data_i;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wdog_bite_thold_q <= 32'd0;
    end else if (wdog_bite_thold_reg_wr_i) begin
      wdog_bite_thold_q <= wdog_bite_thold_d;
    end
  end

  assign wdog_bite_thold_o = wdog_bite_thold_q;

  // Watchdog timer count
  assign wdog_incr     = wdog_enable_q & (lc_cpu_en_i[2] == lc_ctrl_pkg::Off) &
                         ~(sleep_mode_i & wdog_pause_q);
  assign wdog_count_d  = wdog_count_reg_wr_i ? wdog_count_wr_data_i :
                                               (wdog_count_q + 32'd1);
  assign wdog_count_en = wdog_incr | wdog_count_reg_wr_i;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wdog_count_q <= 32'd0;
    end else if (wdog_count_en) begin
      wdog_count_q <= wdog_count_d;
    end
  end

  assign wdog_count_o = wdog_count_q;

  // Timer interrupt
  assign wdog_intr_o = wdog_incr & (wdog_count_q == wdog_bark_thold_q);
  // Timer reset
  assign wdog_reset_req_o = wdog_incr & (wdog_count_q == wdog_bite_thold_q);

endmodule
