// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Simple EEPROM BFM for testing SPI Host module.
//
//

module spi_eeprom_bfm #(
  parameter int   Size  = 256,
  parameter int   AddrW = $clog2(Size),
  parameter       MemInitFile = ""
) (
  input  rst_ni,
  input  sck_i,
  input  csb_i,
  input  sd_i,
  output sd_o
);

  localparam logic [7:0] OpCodeSFDP = 8'h5a;

  logic [7:0] sr_i_d, sr_i_q;
  logic [7:0] sr_o_q, sr_o_d;

  assign sr_i_d = { sr_i_q[6:0], sd_i };

  logic [2:0] bit_cntr_q, bit_cntr_d;
  logic [8:0] byte_cntr_q, byte_cntr_d;

  assign bit_cntr_d = csb_i ? 3'h7 :
                      (bit_cntr_q == 3'h0) ? 3'h7 :
                      bit_cntr_q - 1;

  assign sd_o = sr_o_q[bit_cntr_q];

  assign byte_cntr_d = csb_i ? 1'b0 :
                       (bit_cntr_q == 3'h0) ? byte_cntr_q + 1 :
                       byte_cntr_q;

  logic               do_process_input;
  assign do_process_input = ~csb_i & (bit_cntr_q == 8'h0);

  logic               rst_int_n;
  assign rst_int_n = ~csb_i & rst_ni;

  typedef enum logic [2:0] {
    Init,
    InvalidCmd,
    Address2,
    Address1,
    Address0,
    ReadEn
  } spfd_st_e;

  spfd_st_e state_q, state_d;

  logic [23:0] full_address_d, full_address_q;

  logic [AddrW-1:0] address;
  assign address = full_address_d[AddrW-1:0];

  logic [7:0] sfdp_data;

  prim_rom_pkg::rom_cfg_t unused_cfg;
  assign unused_cfg = '0;

  prim_generic_rom #(
    .Width(8),
    .Depth(Size),
    .MemInitFile(MemInitFile)
  ) u_sfdp_rom (
    .clk_i(~sck_i),
    .req_i(do_process_input),
    .addr_i(address),
    .rdata_o(sfdp_data),
    .cfg_i(unused_cfg)
  );

  always_comb begin
    state_d = state_q;
    full_address_d = full_address_q;
    sr_o_d = sr_o_q;
    if (do_process_input) begin
      unique case (state_q)
        Init: begin
          if (sr_i_q == OpCodeSFDP) begin
            state_d = Address2;
          end else begin
            state_d = InvalidCmd;
          end
        end
        InvalidCmd: begin
          state_d = InvalidCmd;
        end
        Address2: begin
          full_address_d = {16'h0, sr_i_q};
          state_d = Address1;
        end
        Address1: begin
          full_address_d = {full_address_q[15:0], sr_i_q};
          state_d = Address0;
        end
        Address0: begin
          full_address_d = {full_address_q[15:0], sr_i_q};
          state_d = ReadEn;
        end
        ReadEn: begin
          full_address_d = full_address_q + 1;
          state_d = ReadEn;
          sr_o_d = sfdp_data;
        end
        default: begin
          state_d = InvalidCmd;
        end
      endcase
    end
  end

  // Armed: Support both mode 0 (CPOL=0/CPHA=0) and mode 3 (CPOL=1/CPHA=1) operation by ignoring
  // falling edges of sck_i until at least one rising edge is detected after csb_i drops.
  logic               armed;

  // Most state processing is done on falling edge of sck_i.
  //
  // Exceptions:
  // Inputs are latched in on sck_i rising edge.
  // FSM is armed after first rising edge after csb_i drops.

  always_ff @(negedge sck_i, negedge rst_int_n) begin
    if (!rst_int_n) begin
      bit_cntr_q     <= 3'h7;
      byte_cntr_q    <= 8'h0;
      state_q        <= Init;
      full_address_q <= 24'b0;
      sr_o_q         <= 8'h0;
    end else begin
      bit_cntr_q     <= armed ? bit_cntr_d  : bit_cntr_q;
      byte_cntr_q    <= byte_cntr_d;
      state_q        <= state_d;
      full_address_q <= full_address_d;
      sr_o_q         <= sr_o_d;
    end
  end

  always_ff @(posedge sck_i, negedge rst_int_n) begin
    if (!rst_int_n) begin
      sr_i_q <= 8'h0;
      armed <= 1'b0;
    end else begin
      sr_i_q <= sr_i_d;
      armed <= 1'b1;
    end
  end

endmodule
