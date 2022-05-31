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
  parameter int unsigned StatusW = 24
) (
  input clk_i,
  input rst_ni,

  input clk_out_i, // Output clock (inverted SCK)

  input clk_csb_i, // CSb clock source

  input sys_clk_i, // Handling STATUS CSR (ext type)
  input sys_rst_ni,

  input sys_csb_deasserted_pulse_i, // to latch committed status

  // status register from CSR: sys_clk domain
  // bit [          0]: RW0C by SW / W1S by HW
  // bit [StatusW-1:1]: RW
  input                      sys_status_we_i,
  input  logic [StatusW-1:0] sys_status_i,
  output logic [StatusW-1:0] sys_status_o, // sys_clk domain

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

  // WREN set/ clear
  input inclk_we_set_i,
  input inclk_we_clr_i,

  // indicator of busy for other HW. Mainly to block passthrough
  output logic csb_busy_broadcast_o // SCK domain
);

  ///////////////
  // Temporary //
  ///////////////

  logic unused_cmd_info;
  assign unused_cmd_info = ^cmd_info_i;

  logic unused_p2s_sent;
  assign unused_p2s_sent = outclk_p2s_sent_i;

  assign io_mode_o = SingleIO;

  typedef enum logic {
    StIdle,
    StActive
  } st_e;
  st_e st_q, st_d;

  typedef enum int unsigned {
    BitBusy      = 0, // BUSY bit [0]
    BitWe        = 1  // WEL  bit [1]
  } status_bit_e;

  ////////////
  // Signal //
  ////////////
  logic [StatusW-1:0] sck_status_committed;
  logic [StatusW-1:0] sck_status_staged;
  logic [StatusW-1:0] sck_sw_status;

  logic      p2s_valid_inclk;
  spi_byte_t p2s_byte_inclk;

  // FIFO rvalid , rready
  logic sck_sw_we, sck_sw_ack;
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

  // Design Doc
  //  https://docs.google.com/document/d/1wUIynMYVfVg9HmCL0q5-6r9BuN-XM0z--wGqU0bXRQ0

  // assumes BUSY bit as 0
  `ASSERT_INIT(BusyBitZero_A, BitBusy == 0)

  // BUSY status in SCK
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sck_status_staged[BitBusy] <= 1'b 0;
    end else if (sck_sw_we && (sck_sw_status[BitBusy] == 1'b 0)) begin
      sck_status_staged[BitBusy] <= 1'b 0;
    end else if (inclk_busy_set_i) begin
      sck_status_staged[BitBusy] <= 1'b 1;
    end
  end

  // WEL handling
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sck_status_staged[BitWe] <= 1'b 0;
    end else if (inclk_we_set_i) begin
      sck_status_staged[BitWe] <= 1'b 1;
    end else if (inclk_we_clr_i) begin
      sck_status_staged[BitWe] <= 1'b 0;
    end else if (sck_sw_we) begin
      sck_status_staged[BitWe] <= sck_sw_status[BitWe];
    end
  end

  // Rest of Status
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sck_status_staged[StatusW-1:BitWe+1] <= '0;
    end else if (sck_sw_we) begin
      sck_status_staged[StatusW-1:BitWe+1] <= sck_sw_status[StatusW-1:BitWe+1];
    end
  end

  // Staged to Comitted at CSb de-assertion
  prim_flop #(
    .Width      ($bits(sck_status_staged)),
    .ResetValue ('0)
  ) u_stage_to_commit (
    .clk_i  (clk_csb_i),
    .rst_ni (sys_rst_ni),
    .d_i    (sck_status_staged),
    .q_o    (sck_status_committed)
  );
  // busy_broadcast
  assign csb_busy_broadcast_o = sck_status_committed[BitBusy];

  // Status in SCK
  assign sck_sw_ack = 1'b 1; // always accept when clock is valid.

  prim_fifo_async #(
    .Width             (StatusW),
    .Depth             (2),
    .OutputZeroIfEmpty (1'b 1)
  ) u_sw_status_update_sync (
    .clk_wr_i  (sys_clk_i      ),
    .rst_wr_ni (sys_rst_ni     ),
    .wvalid_i  (sys_status_we_i),
    .wready_o  (               ), // ignore
    .wdata_i   (sys_status_i   ),
    .wdepth_o  (               ),

    .clk_rd_i  (clk_i        ),
    .rst_rd_ni (sys_rst_ni   ),
    .rvalid_o  (sck_sw_we    ),
    .rready_i  (sck_sw_ack   ),
    .rdata_o   (sck_sw_status),
    .rdepth_o  (             )
  );

  // Committed to SYS clk
  // Update with csb release event (pulse), which always will be delayed two
  // SYS cycles. Then it is safe to use comitted register.
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sys_status_o <= '0;
    end else if (sys_csb_deasserted_pulse_i) begin
      sys_status_o <= sck_status_committed;
    end
  end

  /////////////////
  // Data Return //
  /////////////////

  // Latch in clk_out
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outclk_p2s_valid_o <= 1'b 0;
      outclk_p2s_byte_o  <= '0;
    end else begin
      outclk_p2s_valid_o <= p2s_valid_inclk;
      outclk_p2s_byte_o  <= p2s_byte_inclk;
    end
  end

  // cmd_idx to data selector
  logic [1:0] byte_sel_d, byte_sel_q;
  logic byte_sel_update, byte_sel_inc;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      byte_sel_q <= 2'b 00;
    end else begin
      byte_sel_q <= byte_sel_d;
    end
  end

  always_comb begin : byte_sel_input
    byte_sel_d = byte_sel_q;

    if (byte_sel_update) begin
      // Check input command index and assign initial byte_sel
      byte_sel_d = 2'b 00; // default value

      for (int unsigned i = 0 ; i <= 2 ; i++) begin
        if (cmd_info_idx_i == CmdInfoIdxW'(StatusCmdIdx[i])) begin
          byte_sel_d = i;
        end
      end
    end else if (byte_sel_inc) begin
      unique case (byte_sel_q)
        2'b 00:  byte_sel_d = 2'b 01;
        2'b 01:  byte_sel_d = 2'b 10;
        2'b 10:  byte_sel_d = 2'b 00;
        default: byte_sel_d = 2'b 00;
      endcase
    end
  end : byte_sel_input

  assign p2s_byte_inclk = (st_q == StIdle)
                        ? sck_status_committed[8*byte_sel_d+:8]
                        : sck_status_committed[8*byte_sel_q+:8];

  // State Machine

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StIdle;
    else         st_q <= st_d;
  end

  always_comb begin
    st_d = st_q;

    byte_sel_update = 1'b 0;
    byte_sel_inc    = 1'b 0;

    p2s_valid_inclk = 1'b 0;

    unique case (st_q)
      StIdle: begin
        if (sel_dp_i == DpReadStatus) begin
          st_d = StActive;
          // dp asserted after 8th SCK. Should send out the data right away.
          byte_sel_update = 1'b 1;
          p2s_valid_inclk = 1'b 1;
        end
      end

      StActive: begin
        p2s_valid_inclk = 1'b 1;
        // deadend state
        // Everytime a byte sent out, shift to next.

        // Check if the byte_sel_inc to be delayed a cycle
        // p2s_sent is asserted at 7th beat not 8th beat.
        // But the spi_p2s module stores prev data into its 8bit register.
        // So increasing the selection signal does not affect current SPI byte.
        if (outclk_p2s_sent_i) byte_sel_inc = 1'b 1;
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

endmodule : spid_status
