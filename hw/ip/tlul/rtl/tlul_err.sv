// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


`include "prim_assert.sv"

module tlul_err import tlul_pkg::*; (
  input clk_i,
  input rst_ni,

  input tl_h2d_t tl_i,

  output logic err_o
);

  localparam int IW  = $bits(tl_i.a_source);
  localparam int SZW = $bits(tl_i.a_size);
  localparam int DW  = $bits(tl_i.a_data);
  localparam int MW  = $bits(tl_i.a_mask);
  localparam int SubAW = $clog2(DW/8);

  logic opcode_allowed, a_config_allowed;

  logic op_full, op_partial, op_get;
  assign op_full    = (tl_i.a_opcode == PutFullData);
  assign op_partial = (tl_i.a_opcode == PutPartialData);
  assign op_get     = (tl_i.a_opcode == Get);

  // An instruction type transaction cannot be write
  logic instr_wr_err;
  assign instr_wr_err = prim_mubi_pkg::mubi4_test_true_strict(tl_i.a_user.instr_type) &
                        (op_full | op_partial);

  logic instr_type_err;
  assign instr_type_err = prim_mubi_pkg::mubi4_test_invalid(tl_i.a_user.instr_type);

  // Anything that doesn't fall into the permitted category, it raises an error
  assign err_o = ~(opcode_allowed & a_config_allowed) | instr_wr_err | instr_type_err;

  // opcode check
  assign opcode_allowed = (tl_i.a_opcode == PutFullData)
                        | (tl_i.a_opcode == PutPartialData)
                        | (tl_i.a_opcode == Get);

  // a channel configuration check
  logic addr_sz_chk;    // address and size alignment check
  logic mask_chk;       // inactive lane a_mask check
  logic fulldata_chk;   // PutFullData should have size match to mask

  logic [MW-1:0] mask;

  assign mask = (1 << tl_i.a_address[SubAW-1:0]);

  always_comb begin
    addr_sz_chk  = 1'b0;
    mask_chk     = 1'b0;
    fulldata_chk = 1'b0; // Only valid when opcode is PutFullData

    if (tl_i.a_valid) begin
      unique case (tl_i.a_size)
        'h0: begin // 1 Byte
          addr_sz_chk  = 1'b1;
          mask_chk     = ~|(tl_i.a_mask & ~mask);
          fulldata_chk = |(tl_i.a_mask & mask);
        end

        'h1: begin // 2 Byte
          addr_sz_chk  = ~tl_i.a_address[0];
          // check inactive lanes if lower 2B, check a_mask[3:2], if uppwer 2B, a_mask[1:0]
          mask_chk     = (tl_i.a_address[1]) ? ~|(tl_i.a_mask & 4'b0011)
                       : ~|(tl_i.a_mask & 4'b1100);
          fulldata_chk = (tl_i.a_address[1]) ? &tl_i.a_mask[3:2] : &tl_i.a_mask[1:0] ;
        end

        'h2: begin // 4 Byte
          addr_sz_chk  = ~|tl_i.a_address[SubAW-1:0];
          mask_chk     = 1'b1;
          fulldata_chk = &tl_i.a_mask[3:0];
        end

        default: begin // else
          addr_sz_chk  = 1'b0;
          mask_chk     = 1'b0;
          fulldata_chk = 1'b0;
        end
      endcase
    end else begin
      addr_sz_chk  = 1'b0;
      mask_chk     = 1'b0;
      fulldata_chk = 1'b0;
    end
  end

  assign a_config_allowed = addr_sz_chk
                          & mask_chk
                          & (op_get | op_partial | fulldata_chk) ;

  // Only 32 bit data width for current tlul_err
  `ASSERT_INIT(dataWidthOnly32_A, DW == 32)

endmodule
