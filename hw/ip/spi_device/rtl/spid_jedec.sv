// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash Read JEDEC ID handler

`include "prim_assert.sv"

module spid_jedec
  import spi_device_pkg::*;
(
  input clk_i,
  input rst_ni,

  input clk_out_i, // Output clock (inverted SCK)

  input inclk_csb_asserted_pulse_i,

  input jedec_cfg_t sys_jedec_i, // from CSR

  output io_mode_e io_mode_o,

  input sel_datapath_e          sel_dp_i,
  input cmd_info_t              cmd_info_i,
  input logic [CmdInfoIdxW-1:0] cmd_info_idx_i,

  output logic      outclk_p2s_valid_o,
  output spi_byte_t outclk_p2s_byte_o,
  input  logic      outclk_p2s_sent_i
);

  typedef enum logic [1:0] {
    StIdle,

    // If num_cc is non-zero, State machine moves to CC state and sends CC up
    // to num_cc times.
    StCC,

    // In JedecId state, the logic sends manufacturer ID (jedec.jedec_id)
    StJedecId,

    // After sending a byte at StJedecId, the logic returns 2 DevId bytes to
    // the host system.
    StDevId
  } st_e;
  st_e st_q, st_d;

  ////////////
  // Signal //
  ////////////

  assign io_mode_o = SingleIO;

  jedec_cfg_t jedec;

  logic      p2s_valid;
  spi_byte_t p2s_byte;

  logic next_byte;
  logic [1:0] byte_sel_q, byte_sel_d;

  // Unused
  logic unused_cmd_info;
  assign unused_cmd_info = ^{cmd_info_i , cmd_info_idx_i};

  //////////////
  // Datapath //
  //////////////

  // Jedec latch
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                         jedec <= '{default: '0};
    else if (inclk_csb_asserted_pulse_i) jedec <= sys_jedec_i;
  end

  // If num_cc is non-zero, the logic shall return CC first
  logic cc_needed;
  assign cc_needed = |jedec.num_cc;

  logic [7:0] cc_count;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) cc_count <= '0;
    else if (st_q == StCC && outclk_p2s_sent_i) begin
      cc_count <= cc_count + 1'b 1;
    end
  end

  // Output to Parallel-to-Serial
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outclk_p2s_valid_o <= 1'b 0;
      outclk_p2s_byte_o  <= 8'h 0;
    end else begin
      outclk_p2s_valid_o <= p2s_valid;
      outclk_p2s_byte_o  <= p2s_byte;
    end
  end

  always_comb begin : p2s_byte_logic
    p2s_byte = 8'h 0;

    if (st_q == StIdle) begin
      // Manufacturer ID always
      p2s_byte = (cc_needed) ? jedec.cc : jedec.jedec_id;
    end else if (st_q == StCC) begin
      p2s_byte = jedec.cc;
    end else if (st_q == StJedecId) begin
      p2s_byte = jedec.jedec_id;
    end else begin
      // based on byte_sel_q
      // End of the transfer but host keep toggles SCK. Sending out 0 always
      p2s_byte = (byte_sel_q >= 2'b 10) ? 8'h 0 :
                 (byte_sel_q == 2'b 01) ? jedec.device_id[15:8] :
                                          jedec.device_id[7:0] ;
    end
  end : p2s_byte_logic

  // Byte selection
  always_ff @(posedge clk_i or negedge rst_ni) begin : byte_sel_latch
    if (!rst_ni)        byte_sel_q <= 8'h 0; // select manufacturer id
    else if (next_byte) byte_sel_q <= byte_sel_d;
  end : byte_sel_latch

  assign byte_sel_d = (byte_sel_q == 2'b 10) ? 2'b 10 : byte_sel_q + 1'b 1;

  ///////////
  // State //
  ///////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_latch
    if (!rst_ni) st_q <= StIdle;
    else         st_q <= st_d;
  end : state_latch

  `ASSERT_KNOWN(JedecStKnown_A, st_q)
  always_comb begin : next_state_logic
    st_d = st_q;

    p2s_valid = 1'b 0;
    next_byte = 1'b 0;

    unique case (st_q)
      StIdle: begin
        if (sel_dp_i == DpReadJEDEC) begin
          st_d = (cc_needed) ? StCC : StJedecId ;

          // Send out the dat
          p2s_valid = 1'b 1;
        end
      end

      StCC: begin

        // cc_count is increased by 1 when outclk_p2s_sent_i is asserted
        // outclk_p2s_sent_i asserts at the 7th beat, not 8th beat.  When
        // cc_count reaches to num_cc, it is the end of a byte transaction in
        // SCK input clock domain. So, that time state machine moves to
        // JedecId
        if (cc_count == jedec.num_cc) begin
          st_d = StJedecId;
        end

        p2s_valid = 1'b 1;
      end

      StJedecId: begin
        if (outclk_p2s_sent_i) begin
          st_d = StDevId;
        end

        p2s_valid = 1'b 1;
      end

      StDevId: begin
        // TERMINAL_STATE

        // Sends data
        p2s_valid = 1'b 1;

        if (outclk_p2s_sent_i) begin
          next_byte = 1'b 1;
        end
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end : next_state_logic

endmodule : spid_jedec
