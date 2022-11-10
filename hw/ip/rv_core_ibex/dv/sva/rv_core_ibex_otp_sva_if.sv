// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This checks the interaction of Ibex with the OTP scramble interface.
interface rv_core_ibex_otp_sva_if #(
  parameter bit ICache          = 1'b1,
  parameter bit ICacheScramble  = 1'b1
) (
  // Ibex signals
  input logic                                                 ibex_decoder_instr_valid,
  input logic [31:0]                                          ibex_decoder_instr,
  input ibex_pkg::opcode_e                                    ibex_decoder_opcode,
  input logic [ibex_pkg::IC_NUM_WAYS-1:0]                     ibex_icache_tag_bank_key_valid,
  input otp_ctrl_pkg::sram_key_t [ibex_pkg::IC_NUM_WAYS-1:0]  ibex_icache_tag_bank_key,
  input logic [ibex_pkg::IC_NUM_WAYS-1:0]                     ibex_icache_data_bank_key_valid,
  input otp_ctrl_pkg::sram_key_t [ibex_pkg::IC_NUM_WAYS-1:0]  ibex_icache_data_bank_key,
  // OTP ports
  input logic                                                 otp_clk_i,
  input logic                                                 otp_rst_ni,
  input logic                                                 otp_sram_otp_key_i_req,
  input logic                                                 otp_sram_otp_key_o_ack,
  input otp_ctrl_pkg::sram_key_t                              otp_sram_otp_key_o_key
);

  if (ICache && ICacheScramble) begin : gen_icache_scramble_asserts

    // Sample icache scramble key for use in assertions below.
    // pragma coverage off
    //VCS coverage off
    otp_ctrl_pkg::sram_key_t icache_otp_key_q;
    always_ff @(posedge otp_clk_i, negedge otp_rst_ni) begin
      if (!otp_rst_ni) begin
        icache_otp_key_q <= '0;
      end else if (otp_sram_otp_key_o_ack) begin
        icache_otp_key_q <= otp_sram_otp_key_o_key;
      end
    end
    //VCS coverage on
    // pragma coverage on

    // Ensure that when a scramble key is received, it is correctly applied to the icache scrambled
    // memory primitives.
    for (genvar way = 0; way < ibex_pkg::IC_NUM_WAYS; way++) begin : gen_ways
      `ASSERT(IbexIcacheScrambleKeyAppliedAtTagBank_A,
          otp_sram_otp_key_o_ack
          |-> ##[0:24] // upper bound is not exact, but it shouldn't take more than two dozen cycles
          ibex_icache_tag_bank_key_valid[way]
          && (ibex_icache_tag_bank_key[way] == icache_otp_key_q)
      )
      `ASSERT(IbexIcacheScrambleKeyAppliedAtDataBank_A,
          otp_sram_otp_key_o_ack
          |-> ##[0:24] // upper bound is not exact, but it shouldn't take more than two dozen cycles
          ibex_icache_data_bank_key_valid[way]
          && (ibex_icache_data_bank_key[way] == icache_otp_key_q)
      )
    end

    // Ensure that when a FENCE.I is executed, a new icache scramble key is requested.
    `ASSERT(IbexIcacheScrambleKeyRequestAfterFenceI_A,
        ibex_decoder_instr_valid
        && ibex_decoder_opcode == ibex_pkg::OPCODE_MISC_MEM
        && ibex_decoder_instr[14:12] == 3'b001 // FENCE.I
        |-> ##[0:24] // upper bound is not exact, but it shouldn't take more than two dozen cycles
        otp_sram_otp_key_i_req
    )

  end

endinterface
