// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C finite state machine

module i2c_fsm (
  input        clk_i,
  input        rst_ni,

  input        scl_i,
  output       scl_o,
  input        sda_i,
  output       sda_o,

  input        fmt_fifo_rvalid,
  output       fmt_fifo_rready,
  input [7:0]  fmt_byte,
  input        fmt_flag_start_before,
  input        fmt_flag_stop_after,
  input        fmt_flag_read_bytes,
  input        fmt_flag_read_continue,
  input        fmt_flag_nak_ok,

  output       rx_fifo_wvalid,
  output [7:0] rx_fifo_wdata,

  output       host_idle,

  input [15:0] thigh,
  input [15:0] tlow,
  input [15:0] t_r,
  input [15:0] t_f,
  input [15:0] thd_sta,
  input [15:0] tsu_sta,
  input [15:0] tsu_sto,
  input [15:0] tsu_dat,
  input [15:0] thd_dat,
  input [15:0] t_buf,
  input [30:0] stretch_timeout,
  input        timeout_enable,

  output       event_nak,
  output       event_scl_interference,
  output       event_sda_interference,
  output       event_stretch_timeout,
  output       event_sda_unstable
);

  // PLACEHOLDER IO
  assign scl_o = 1'b0;
  assign sda_o = 1'b0;
  assign fmt_fifo_rready = 1'b0;
  assign rx_fifo_wvalid = 1'b0;
  assign rx_fifo_wdata = 8'h00;

  assign event_nak              = 1'b0;
  assign event_scl_interference = 1'b0;
  assign event_sda_interference = 1'b0;
  assign event_stretch_timeout  = 1'b0;
  assign event_sda_unstable     = 1'b0;

endmodule;
