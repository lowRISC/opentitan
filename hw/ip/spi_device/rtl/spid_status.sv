// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash Read Status handler
/*
*/

`include "prim_assert.sv"

module spid_status
  import spi_device_pkg::*;
#(
  // Read Status module recognizes the command by the cmd_info_idx from the
  // cmdparse logic as the Opcode of the command could vary. Use the index and
  // determines the return order of the status register.
  parameter int unsigned StatusCmdIdx[3] = '{
    spi_device_pkg::CmdInfoReadStatus1,
    spi_device_pkg::CmdInfoReadStatus2,
    spi_device_pkg::CmdInfoReadStatus3
  },
  parameter int unsigned CmdInfoIdxW = spi_device_pkg::CmdInfoIdxW
) (
  input clk_i,
  input rst_ni,

  input sys_clk_i, // Handling STATUS CSR (ext type)
  input sys_rst_ni,

  input csb_i, // CSb as a signal (not as a reset)

  // status register from CSR: sys_clk domain
  // bit [   0]: RW0C by SW / W1S by HW
  // bit [23:1]: RW
  input               sys_status_we_i,
  input  logic [23:0] sys_status_i,
  output logic [23:0] sys_status_o, // sys_clk domain

  // from cmdparse
  input sel_datapath_e          sel_dp_i,
  input cmd_info_t              cmd_info_i,
  input logic [CmdInfoIdxW-1:0] cmd_info_idx_i,

  output logic      outclk_p2s_valid_o,
  output spi_byte_t outclk_p2s_byte_o,
  input  logic      outclk_p2s_sent_i,

  output io_mode_e io_mode_o,

  // receives the busy from other HW
  input inclk_busy_set_i, // SCK domain

  // indicator of busy for other HW. Mainly to block passthrough
  output logic inclk_busy_broadcast_o // SCK domain
);

  ///////////////
  // Temporary //
  ///////////////
  sel_datapath_e unused_dp;
  assign unused_dp = sel_dp_i;

  logic unused_cmd_info;
  assign unused_cmd_info = ^{cmd_info_i, cmd_info_idx_i};

  logic unused_p2s_sent;
  assign unused_p2s_sent = outclk_p2s_sent_i;

  assign outclk_p2s_valid_o = 1'b 0;
  assign outclk_p2s_byte_o  = '0;

  assign io_mode_o = SingleIO;

  ////////////
  // Signal //
  ////////////
  logic [23:0] status_sck;

  logic unused_status_sck;
  assign unused_status_sck = ^status_sck;


  ////////////////////////////
  // Status CSR (incl. CDC) //
  ////////////////////////////
  //
  // Flash mode STATUS register is implemented in this module rather than
  // relying on the regtool. The reason is that the STATUS read by the SPI
  // host system. The value should be propagated into SCK domain. Due to the
  // lack of SCK while CSb is de-asserted, it needs special cares to safely
  // used in SCK.
  //
  // Before returning the STATUS register value to the host system
  // corresponding to the Read Status commands (05h, 35h, 15h), the logic can
  // get 8 SCK clock edges. The logic synchronizes CSb into SCK domain first.
  // Then create a pulse to latch the STATUS register in SCK domain.
  //
  // If a command is uploaded (handled by spid_upload), it sets BUSY bit to 1.
  // The value is latched in the SCK domain first. Then, when CSb is
  // de-asserted, the logic synchronizes CSb into the bus clock domain to
  // create a pulse signal. That pulse signal will latch the STATUS register
  // from SCK domain into the bus clock domain.
  //
  // The STATUS register in the bus clock domain can be updated only when CSb
  // is not asserted in order to prevent any CDC issue. The safest way is to
  // hand the busclock synched CSb signal over to SCK clock domain again but
  // it may not be possible to latch the register within the 8th posedge of
  // the SCK if the bus clock is slow.
  //
  // BUSY is set by HW. The value is not directly broadcasted to the
  // passthrough module. It is, first, applied into the bus clock domain. Then
  // the signal is broadcasted to Passthrough to filter-out the following
  // commands until the BUSY signal is released.

  logic reg_en; // If 1, register in bus clock domain can be updated by SW
  logic reg_update; // indicator of HW update (when CSb is de-asserted)

  // Register interface update in bus clock domain
  logic [23:0] status;
  //  BUSY
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      status[0] <= 1'b 0;
    end else if (reg_en && sys_status_we_i && (1'b0 == sys_status_i[0])) begin
      status[0] <= 1'b 0;
    end else if (reg_update) begin
      // TODO: Latch HW value to here
      status[0] <= status_sck[0];
    end
  end
  //  rest of STATUS
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      status[23:1] <= '0;
    end else if (reg_en && sys_status_we_i) begin
      status[23:1] <= sys_status_i[23:1];
    end
  end

  assign sys_status_o = status;

  // busy_broadcast
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 0)
  ) u_busy_sync (
    .clk_i,
    .rst_ni,
    .d_i (status[0]),
    .q_o (inclk_busy_broadcast_o)
  );

  // CSb pulse
  logic csb_sync_d, csb_sync_q, csb_asserted_pulse;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sync (
    .clk_i,
    .rst_ni, //Use CSb as a reset
    .d_i (1'b 0),
    .q_o (csb_sync_d)
  );
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) csb_sync_q <= 1'b 1;
    else         csb_sync_q <= csb_sync_d;
  end

  assign csb_asserted_pulse = csb_sync_q && !csb_sync_d;

  // CSb de-asserted pulse is used as reg_update.
  // TODO: merge this to the top then receive the signal through the module
  // port?
  logic reg_en_q;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sync_sysclk (
    .clk_i  (sys_clk_i),
    .rst_ni (sys_rst_ni),
    .d_i    (csb_i),
    .q_o    (reg_en)
  );
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) reg_en_q <= 1'b 1;
    else             reg_en_q <= reg_en;
  end
  assign reg_update = !reg_en_q && reg_en;

  // Status in SCK
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      status_sck <= 24'h 0;
    end else if (csb_asserted_pulse) begin
      status_sck <= status;
    end else if (inclk_busy_set_i) begin
      status_sck[0] <= 1'b 1;
    end
  end

endmodule : spid_status
