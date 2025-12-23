// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Compressed instruction decoder
 *
 * Decodes RISC-V compressed instructions into their RV32 equivalent.
 * This module is fully combinatorial, clock and reset are used for
 * assertions only.
 */

`include "prim_assert.sv"

module ibex_compressed_decoder #(
  parameter ibex_pkg::rv32zc_e RV32ZC   = ibex_pkg::RV32ZcaZcbZcmp,
  parameter bit                ResetAll = 1'b0
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic                 valid_i,
  input  logic                 id_in_ready_i,
  input  logic [31:0]          instr_i,
  output logic [31:0]          instr_o,
  output logic                 is_compressed_o,
  output ibex_pkg::instr_exp_e gets_expanded_o,
  output logic                 illegal_instr_o
);
  import ibex_pkg::*;

  if (!(RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcmp)) begin : gen_unused_valid
    // valid_i indicates if instr_i is valid and is used for assertions only if Zcmp is disabled.
    // id_in_ready_i indicates if instr_o is consumed and is used for assertions only if Zcmp is
    // disabled. The following signals are used to avoid possible lint errors.
    logic unused_valid;
    logic unused_id_in_ready;
    assign unused_valid = valid_i;
    assign unused_id_in_ready = id_in_ready_i;
  end

  function automatic logic [6:0] cm_stack_adj_base(input logic [3:0] rlist);
    unique case (rlist)
      // Deliberately not written as `case .. inside` because that is not supported by all tools.
      4'd4, 4'd5, 4'd6, 4'd7:   return 7'd16;
      4'd8, 4'd9, 4'd10, 4'd11: return 7'd32;
      4'd12, 4'd13, 4'd14:      return 7'd48;
      4'd15:                    return 7'd64;
      default:                  return 7'd0; // illegal
    endcase
  endfunction

  function automatic logic [6:0] cm_stack_adj(input logic [3:0] rlist, input logic [1:0] spimm);
    return cm_stack_adj_base(rlist) + spimm * 16;
  endfunction

  function automatic logic [4:0] cm_stack_adj_word(input logic [3:0] rlist,
                                                   input logic [1:0] spimm);
    logic [6:0] tmp;
    logic [1:0] _unused;
    tmp = cm_stack_adj(.rlist(rlist), .spimm(spimm));
    _unused = tmp[1:0];
    return tmp[6:2];
  endfunction

  function automatic logic [4:0] cm_rlist_top_reg(input logic [4:0] rlist);
    unique case (rlist)
      // Deliberately not written as `case .. inside` because that is not supported by all tools.
      5'd16, // `rlist` can be 16 after instruction decoding, to handle `x26`+`x27`.
      5'd15, 5'd14, 5'd13,
      5'd12, 5'd11, 5'd10,
      5'd9, 5'd8, 5'd7:     return 5'd11 + rlist;
      5'd6, 5'd5:           return 5'd3 + rlist;
      5'd4:                 return 5'd1;
      default:              return 5'd0; // illegal
    endcase
  endfunction

  function automatic logic [31:0] cm_push_store_reg(input logic [4:0] rlist,
                                                    input logic [4:0] sp_offset);
    logic [11:0] neg_offset;
    logic [31:0] instr;
    neg_offset = ~{5'b00000, sp_offset, 2'b00} + 12'd1;
    instr[ 6: 0] /* opcode       */ = OPCODE_STORE;
    instr[11: 7] /* offset[4:0]  */ = neg_offset[4:0];
    instr[14:12] /* width        */ = 3'b010; // 32 bit
    instr[19:15] /* base reg     */ = 5'd2; // x2 (sp / stack pointer)
    instr[24:20] /* src reg      */ = cm_rlist_top_reg(rlist);
    instr[31:25] /* offset[11:5] */ = neg_offset[11:5];
    return instr;
  endfunction

  function automatic logic [31:0] cm_pop_load_reg(input logic [4:0] rlist,
                                                  input logic [4:0] sp_offset);
    logic [31:0] instr;
    instr[ 6: 0] /* opcode       */ = OPCODE_LOAD;
    instr[11: 7] /* dest reg     */ = cm_rlist_top_reg(rlist);
    instr[14:12] /* width        */ = 3'b010; // 32 bit
    instr[19:15] /* base reg     */ = 5'd2; // x2 (sp / stack pointer)
    instr[31:20] /* offset[11:0] */ = {5'b00000, sp_offset, 2'b00};
    return instr;
  endfunction

  function automatic logic [31:0] cm_sp_addi(input logic [3:0] rlist,
                                             input logic [1:0] spimm,
                                             input logic decr = 1'b0);
    logic [11:0] imm;
    logic [31:0] instr;
    imm[11:7] = '0;
    imm[ 6:0] = cm_stack_adj(.rlist(rlist), .spimm(spimm));
    if (decr) imm = ~imm + 12'd1;
    instr[ 6: 0] /* opcode    */ = OPCODE_OP_IMM;
    instr[11: 7] /* dest reg  */ = 5'd2; // x2 (sp / stack pointer)
    instr[14:12] /* funct3    */ = 3'b000; // addi
    instr[19:15] /* src reg   */ = 5'd2; // x2
    instr[31:20] /* imm[11:0] */ = imm;
    return instr;
  endfunction

  function automatic logic [31:0] cm_mv_reg(input logic [4:0] src, input logic [4:0] dst);
    logic [31:0] instr;
    instr[ 6: 0] /* opcode    */ = OPCODE_OP_IMM;
    instr[11: 7] /* dest reg  */ = dst;
    instr[14:12] /* funct3    */ = 3'b000; // addi
    instr[19:15] /* src reg   */ = src;
    instr[31:20] /* imm[11:0] */ = 12'd0; // 0
    return instr;
  endfunction

  function automatic logic [31:0] cm_zero_a0();
    return cm_mv_reg(.src(5'd0 /* x0 */), .dst(5'd10 /* a0 */));
  endfunction

  function automatic logic [31:0] cm_ret_ra();
    logic [31:0] instr;
    instr[ 6: 0] /* opcode       */ = OPCODE_JALR;
    instr[11: 7] /* dest reg     */ = 5'd0; // x0
    instr[14:12] /* funct3       */ = 3'b000; // jalr
    instr[19:15] /* base reg     */ = 5'd1; // x1 (ra)
    instr[31:20] /* offset[11:0] */ = 12'd0; // 0
    return instr;
  endfunction

  function automatic logic [31:0] cm_mvsa01(input logic a01, input logic [2:0] rs);
    logic [4:0] src, dst;
    src = 5'd10 + {4'd0, a01};
    dst = {(rs[2:1] > 2'd0), (rs[2:1] == 2'd0), rs[2:0]};
    return cm_mv_reg(.src(src), .dst(dst));
  endfunction

  function automatic logic [31:0] cm_mva01s(input logic [2:0] rs, input logic a01);
    logic [4:0] src, dst;
    src = {(rs[2:1] > 2'd0), (rs[2:1] == 2'd0), rs[2:0]};
    dst = 5'd10 + {4'd0, a01};
    return cm_mv_reg(.src(src), .dst(dst));
  endfunction

  function automatic logic [4:0] cm_rlist_init(input logic [3:0] instr_rlist);
    logic [4:0] rlist;
    rlist = {1'b0, instr_rlist};
    if (rlist == 5'd15) begin
      // An `rlist` value of 15 means that x26 and x27 have to be stored.
      // Handle this by initializing `rlist` internally to 16.
      rlist = 5'd16;
    end
    return rlist;
  endfunction

  // Combined FSM state register for Zcmp operations.
  // This single 3-bit enum represents 3 independent FSMs that share the CmIdle state and the
  // resources.
  typedef enum logic [2:0] {
    CmIdle,
    // cm.push
    CmPushStoreReg,
    CmPushDecrSp,
    // cm.pop, cm.popret, cm.popretz
    CmPopLoadReg,
    CmPopIncrSp,
    CmPopZeroA0,
    CmPopRetRa,
    // cm.mvsa01, cm.mva01s
    CmMvSecondReg
  } cm_state_e;
  logic [4:0] cm_rlist_d, cm_rlist_q;
  logic [4:0] cm_sp_offset_d, cm_sp_offset_q;
  cm_state_e  cm_state_d, cm_state_q;

  // Gate the `gets_expanded_o` to ensure that a invalid instruction looking like expandable cm.*
  // instructions will not be stalled/blocked in later control logic because it is waiting for
  // `INSTR_EXPANDED_LAST`.
  ibex_pkg::instr_exp_e gets_expanded;
  if (RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcmp) begin : gen_gets_expanded
    assign gets_expanded_o = valid_i ? gets_expanded : INSTR_NOT_EXPANDED;
  end else begin : gen_gets_expanded
    // `gets_expanded` will be tied to INSTR_NOT_EXPANDED in this case
    assign gets_expanded_o = gets_expanded;
  end

  ////////////////////////
  // Compressed decoder //
  ////////////////////////

  always_comb begin
    // By default, forward incoming instruction, mark it as legal, and don't expand.
    instr_o         = instr_i;
    illegal_instr_o = 1'b0;
    gets_expanded   = INSTR_NOT_EXPANDED;

    // Maintain state of CM FSM.
    cm_rlist_d     = cm_rlist_q;
    cm_sp_offset_d = cm_sp_offset_q;
    cm_state_d     = cm_state_q;

    // Check if incoming instruction is compressed.
    unique case (instr_i[1:0])
      // C0
      2'b00: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.addi4spn -> addi rd', x2, imm
            instr_o = {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5],
                       instr_i[6], 2'b00, 5'h02, 3'b000, 2'b01, instr_i[4:2], {OPCODE_OP_IMM}};
            if (instr_i[12:5] == 8'b0)  illegal_instr_o = 1'b1;
          end

          3'b010: begin
            // c.lw -> lw rd', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12:10], instr_i[6],
                       2'b00, 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], {OPCODE_LOAD}};
          end

          3'b110: begin
            // c.sw -> sw rs2', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12], 2'b01, instr_i[4:2],
                       2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6],
                       2'b00, {OPCODE_STORE}};
          end

          3'b100: begin // loads and stores
            if (RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcb) begin
              unique case (instr_i[12:10])
                3'b000: begin
                    // c.lbu -> lbu  rd', imm(rs1')
                    instr_o = {10'b0, instr_i[5], instr_i[6], 2'b01, instr_i[9:7],
                               3'b100, 2'b01, instr_i[4:2], {OPCODE_LOAD}};
                end

                3'b001: begin
                    unique case (instr_i[6])
                      1'b0: begin
                        // c.lhu -> lhu rd', imm(rs1')
                        instr_o = {10'b0, instr_i[5], 1'b0, 2'b01, instr_i[9:7],
                                   3'b101, 2'b01, instr_i[4:2], {OPCODE_LOAD}};
                      end
                      1'b1: begin
                        // c.lh -> lh rd', imm(rs1')
                          instr_o = {10'b0, instr_i[5], 1'b0, 2'b01, instr_i[9:7],
                                     3'b001, 2'b01, instr_i[4:2], {OPCODE_LOAD}};
                      end

                      default: begin
                        illegal_instr_o = 1'b1;
                      end
                    endcase
                end

                3'b010: begin
                    // c.sb -> sb rs2', imm(rs1')
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7],
                               3'b000, 3'b0, instr_i[5], instr_i[6], {OPCODE_STORE}};
                end

                3'b011: begin
                    unique case (instr_i[6])
                      1'b0: begin
                        // c.sh -> sh rs2', imm(rs1')
                        // The instr_i[6] should always be zero according to the reference
                        instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7],
                                   3'b001, 3'b0, instr_i[5], 1'b0, {OPCODE_STORE}};
                      end
                      1'b1: begin
                        illegal_instr_o = 1'b1;
                      end

                      default: begin
                        illegal_instr_o = 1'b1;
                      end
                    endcase
                end

                default: begin
                  illegal_instr_o = 1'b1;
                end
              endcase // unique case (instr_i[12:10])
            end else begin
              // The Zcb extension is not enabled
              illegal_instr_o = 1'b1;
            end
          end

          3'b001,
          3'b011,
          3'b101,
          3'b111: begin
            illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C1
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b01: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.addi -> addi rd, rd, nzimm
            // c.nop
            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2],
                       instr_i[11:7], 3'b0, instr_i[11:7], {OPCODE_OP_IMM}};
          end

          3'b001, 3'b101: begin
            // 001: c.jal -> jal x1, imm
            // 101: c.j   -> jal x0, imm
            instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6],
                       instr_i[7], instr_i[2], instr_i[11], instr_i[5:3],
                       {9 {instr_i[12]}}, 4'b0, ~instr_i[15], {OPCODE_JAL}};
          end

          3'b010: begin
            // c.li -> addi rd, x0, nzimm
            // (c.li hints are translated into an addi hint)
            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0,
                       3'b0, instr_i[11:7], {OPCODE_OP_IMM}};
          end

          3'b011: begin
            // c.lui -> lui rd, imm
            // (c.lui hints are translated into a lui hint)
            instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], {OPCODE_LUI}};

            if (instr_i[11:7] == 5'h02) begin
              // c.addi16sp -> addi x2, x2, nzimm
              instr_o = {{3 {instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2],
                         instr_i[6], 4'b0, 5'h02, 3'b000, 5'h02, {OPCODE_OP_IMM}};
            end

            if ({instr_i[12], instr_i[6:2]} == 6'b0) illegal_instr_o = 1'b1;
          end

          3'b100: begin
            unique case (instr_i[11:10])
              2'b00,
              2'b01: begin
                // 00: c.srli -> srli rd, rd, shamt
                // 01: c.srai -> srai rd, rd, shamt
                // (c.srli/c.srai hints are translated into a srli/srai hint)
                instr_o = {1'b0, instr_i[10], 5'b0, instr_i[6:2], 2'b01, instr_i[9:7],
                           3'b101, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                if (instr_i[12] == 1'b1)  illegal_instr_o = 1'b1;
              end

              2'b10: begin
                // c.andi -> andi rd, rd, imm
                instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7],
                           3'b111, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
              end

              2'b11: begin
                unique case ({instr_i[12], instr_i[6:5]})
                  3'b000: begin
                    // c.sub -> sub rd', rd', rs2'
                    instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7],
                               3'b000, 2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b001: begin
                    // c.xor -> xor rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b100,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b010: begin
                    // c.or  -> or  rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b110,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b011: begin
                    // c.and -> and rd', rd', rs2'
                    instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b111,
                               2'b01, instr_i[9:7], {OPCODE_OP}};
                  end

                  3'b100,
                  3'b101: begin
                    // 100: c.subw
                    // 101: c.addw
                    illegal_instr_o = 1'b1;
                  end

                  3'b110: begin
                    if (RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcb) begin
                      // c.mul -> m.mul rsd', rsd', rs2'
                      instr_o = {7'b0000001, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7],
                                 3'b000, 2'b01, instr_i[9:7], {OPCODE_OP}};
                    end else begin
                      // The Zcb extension is not enabled
                      illegal_instr_o = 1'b1;
                    end
                  end

                  3'b111: begin
                    if (RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcb) begin
                      unique case ({instr_i[4:2]})
                        3'b000: begin
                          // c.zext.b -> andi rsd', rsd', 8'hff
                          instr_o = {4'b0, 8'hff, 2'b01, instr_i[9:7], 3'b111,
                                     2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                        end

                        3'b001: begin
                          // c.sext.b -> sext.b rsd', rsd'
                          instr_o = {7'b0110000, 5'b00100, 2'b01, instr_i[9:7],
                                     3'b001, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                        end

                        3'b010: begin
                          // c.zext.h -> zext.h rsd', rsd'
                          instr_o = {7'b0000100, 5'b0, 2'b01, instr_i[9:7],
                                     3'b100, 2'b01, instr_i[9:7], {OPCODE_OP}};
                        end

                        3'b011: begin
                          // c.sext.h -> sext.h rsd', rsd'
                          instr_o = {7'b0110000, 5'b00101, 2'b01, instr_i[9:7],
                                     3'b001, 2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                        end

                        3'b100: begin
                          // c.zext.w -> add.uw: only valid instruction for RV64 cores
                          illegal_instr_o = 1'b1;
                        end

                        3'b101: begin
                          // c.not -> xori rsd', rsd', -1
                          instr_o = {12'hfff, 2'b01, instr_i[9:7], 3'b100,
                                     2'b01, instr_i[9:7], {OPCODE_OP_IMM}};
                        end

                        default: begin
                          illegal_instr_o = 1'b1;
                        end
                      endcase
                    end else begin
                      // The Zcb extension is not enabled
                      illegal_instr_o = 1'b1;
                    end
                  end

                  default: begin
                    illegal_instr_o = 1'b1;
                  end
                endcase
              end

              default: begin
                illegal_instr_o = 1'b1;
              end
            endcase
          end

          3'b110, 3'b111: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            instr_o = {{4 {instr_i[12]}}, instr_i[6:5], instr_i[2], 5'b0, 2'b01,
                       instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3],
                       instr_i[12], {OPCODE_BRANCH}};
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C2
      //
      // Register address checks for RV32E are performed in the regular instruction decoder.
      // If this check fails, an illegal instruction exception is triggered and the controller
      // writes the actual faulting instruction to mtval.
      2'b10: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.slli -> slli rd, rd, shamt
            // (c.ssli hints are translated into a slli hint)
            instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], {OPCODE_OP_IMM}};
            if (instr_i[12] == 1'b1)  illegal_instr_o = 1'b1; // reserved for custom extensions
          end

          3'b010: begin
            // c.lwsp -> lw rd, imm(x2)
            instr_o = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00, 5'h02,
                       3'b010, instr_i[11:7], OPCODE_LOAD};
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b100: begin
            if (instr_i[12] == 1'b0) begin
              if (instr_i[6:2] != 5'b0) begin
                // c.mv -> add rd/rs1, x0, rs2
                // (c.mv hints are translated into an add hint)
                instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], {OPCODE_OP}};
              end else begin
                // c.jr -> jalr x0, rd/rs1, 0
                instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, {OPCODE_JALR}};
                if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
              end
            end else begin
              if (instr_i[6:2] != 5'b0) begin
                // c.add -> add rd, rd, rs2
                // (c.add hints are translated into an add hint)
                instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], {OPCODE_OP}};
              end else begin
                if (instr_i[11:7] == 5'b0) begin
                  // c.ebreak -> ebreak
                  instr_o = {32'h00_10_00_73};
                end else begin
                  // c.jalr -> jalr x1, rs1, 0
                  instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, {OPCODE_JALR}};
                end
              end
            end
          end

          3'b101: begin
            if (RV32ZC == RV32ZcaZcbZcmp || RV32ZC == RV32ZcaZcmp) begin
              unique casez (instr_i[12:8])
                // cm.push
                5'b11000: begin
                  // This compressed instruction gets expanded into multiple instructions.
                  gets_expanded = INSTR_EXPANDED;
                  unique case (cm_state_q)
                    CmIdle: begin
                      // No cm.push instruction is active yet; start a new one.
                      // Initialize `rlist` to the value provided by the instruction.
                      cm_rlist_d = cm_rlist_init(instr_i[7:4]);
                      // Store the register at the top of `rlist`, which is the highest register in
                      // the list. Then work our way down by decrementing `rlist` each cycle.
                      instr_o = cm_push_store_reg(.rlist(cm_rlist_d), .sp_offset(5'd1));
                      if (cm_rlist_d <= 5'd3) begin
                        // Reserved --> illegal instruction.
                        illegal_instr_o = 1'b1;
                      end else if (cm_rlist_d == 5'd4) begin
                        // Only `ra` has to be stored, which is done in this cycle.  Proceed by
                        // decrementing SP.
                        if (valid_i && id_in_ready_i) begin
                          cm_state_d = CmPushDecrSp;
                        end
                      end else begin
                        // More registers have to be stored.
                        // Remove the current register from `rlist`.
                        cm_rlist_d -= 5'd1;
                        // Initialize SP offset to 2.
                        // We just stored at offset 1 this cycle and will start incrementing the
                        // offset from 2 onwards in CmPushStoreReg next cycle.
                        cm_sp_offset_d = 5'd2;
                        // Proceed with storing registers.
                        if (valid_i && id_in_ready_i) begin
                          cm_state_d = CmPushStoreReg;
                        end
                      end
                    end
                    CmPushStoreReg: begin
                      // Store register at the top of current `rlist`.
                      instr_o = cm_push_store_reg(.rlist(cm_rlist_q), .sp_offset(cm_sp_offset_q));
                      if (id_in_ready_i) begin
                        // Remove top register from `rlist`.
                        cm_rlist_d = cm_rlist_q - 5'd1;
                        // Increment the SP offset.
                        cm_sp_offset_d = cm_sp_offset_q + 5'd1;
                        if (cm_rlist_q == 5'd4) begin
                          // The last register gets stored in this cycle.  Proceed by decrementing
                          // SP.
                          cm_state_d = CmPushDecrSp;
                        end
                      end
                    end
                    CmPushDecrSp: begin
                      // Decrement stack pointer.
                      instr_o = cm_sp_addi(.rlist(instr_i[7:4]), .spimm(instr_i[3:2]), .decr(1'b1));
                      if (id_in_ready_i) begin
                        // This is the final operation, so stop expanding and return to idle.
                        gets_expanded = INSTR_EXPANDED_LAST;
                        cm_state_d = CmIdle;
                      end
                    end
                    default: cm_state_d = CmIdle;
                  endcase
                end

                // cm.pop, cm.popretz, cm.popret
                5'b11010,
                5'b11100,
                5'b11110: begin
                  // This compressed instruction gets expanded into multiple instructions.
                  gets_expanded = INSTR_EXPANDED;
                  unique case (cm_state_q)
                    CmIdle: begin
                      // No cm.pop instruction is active yet; start a new one.
                      // Initialize `rlist` to the value provided by the instruction.
                      cm_rlist_d = cm_rlist_init(instr_i[7:4]);
                      // Initialize SP offset.
                      cm_sp_offset_d = cm_stack_adj_word(.rlist(instr_i[7:4]),
                                                        .spimm(instr_i[3:2])) - 5'd1;
                      // Load the register at the top of `rlist`, which is the highest register in
                      // the list. Then work our way down by decrementing `rlist` each cycle.
                      instr_o = cm_pop_load_reg(.rlist(cm_rlist_d), .sp_offset(cm_sp_offset_d));
                      if (cm_rlist_d <= 5'd3) begin
                        // Reserved --> illegal instruction.
                        illegal_instr_o = 1'b1;
                      end else if (cm_rlist_d == 5'd4) begin
                        // Only `ra` has to be loaded, which is done in this cycle.  Proceed by
                        // incrementing SP.
                        if (valid_i && id_in_ready_i) begin
                          cm_state_d = CmPopIncrSp;
                        end
                      end else begin
                        // More registers have to be loaded.
                        // Remove the current register from `rlist` and decrement the SP offset.
                        cm_rlist_d -= 5'd1;
                        cm_sp_offset_d -= 5'd1;
                        // Proceed with loading registers.
                        if (valid_i && id_in_ready_i) begin
                          cm_state_d = CmPopLoadReg;
                        end
                      end
                    end
                    CmPopLoadReg: begin
                      // Load register at the top of current `rlist`.
                      instr_o = cm_pop_load_reg(.rlist(cm_rlist_q), .sp_offset(cm_sp_offset_q));
                      if (id_in_ready_i) begin
                        // Remove top register from `rlist`.
                        cm_rlist_d = cm_rlist_q - 5'd1;
                        // Decrement the SP offset.
                        cm_sp_offset_d = cm_sp_offset_q - 5'd1;
                        if (cm_rlist_q == 5'd4) begin
                          // The last register gets stored in this cycle.  Proceed by incrementing
                          // SP.
                          cm_state_d = CmPopIncrSp;
                        end
                      end
                    end
                    CmPopIncrSp: begin
                      // Increment stack pointer.
                      instr_o = cm_sp_addi(.rlist(instr_i[7:4]),
                                          .spimm(instr_i[3:2]),
                                          .decr(1'b0));
                      if (id_in_ready_i) begin
                        unique case (instr_i[12:8])
                          5'b11100: cm_state_d = CmPopZeroA0; // cm.popretz
                          5'b11110: cm_state_d = CmPopRetRa;  // cm.popret
                          default: begin // cm.pop
                            // This is the final operation, so stop expanding and return to idle.
                            gets_expanded = INSTR_EXPANDED_LAST;
                            cm_state_d = CmIdle;
                          end
                        endcase
                      end
                    end
                    CmPopZeroA0: begin
                      instr_o = cm_zero_a0();
                      if (id_in_ready_i) begin
                        cm_state_d = CmPopRetRa;
                      end
                    end
                    CmPopRetRa: begin
                      instr_o = cm_ret_ra();
                      if (id_in_ready_i) begin
                        // This is the final operation, so stop expanding and return to idle.
                        gets_expanded = INSTR_EXPANDED_LAST;
                        cm_state_d = CmIdle;
                      end
                    end
                    default: cm_state_d = CmIdle;
                  endcase
                end

                // cm.mvsa01, cm.mva01s
                5'b011??: begin
                  unique case (instr_i[6:5])
                    // cm.mvsa01
                    2'b01: begin
                      // This compressed instruction gets expanded into multiple instructions.
                      gets_expanded = INSTR_EXPANDED;
                      unique case (cm_state_q)
                        CmIdle: begin
                          // No cm.mvsa01 instruction is active yet; start a new one.
                          // Move a0 to register indicated by r1s'.
                          instr_o = cm_mvsa01(.a01(1'b0), .rs(instr_i[9:7]));
                          if (valid_i && id_in_ready_i) begin
                            cm_state_d = CmMvSecondReg;
                          end
                        end
                        CmMvSecondReg: begin
                          // Move a1 to register indicated by r2s'.
                          instr_o = cm_mvsa01(.a01(1'b1), .rs(instr_i[4:2]));
                          if (id_in_ready_i) begin
                            // This is the final operation, so stop expanding and return to idle.
                            gets_expanded = INSTR_EXPANDED_LAST;
                            cm_state_d = CmIdle;
                          end
                        end
                        default: cm_state_d = CmIdle;
                      endcase
                    end

                    // cm.mva01s
                    2'b11: begin
                      // This compressed instruction gets expanded into multiple instructions.
                      gets_expanded = INSTR_EXPANDED;
                      unique case (cm_state_q)
                        CmIdle: begin
                          // No cm.mva01s instruction is active yet; start a new one.
                          // Move register indicated by r1s' into a0.
                          instr_o = cm_mva01s(.rs(instr_i[9:7]), .a01(1'b0));
                          if (valid_i && id_in_ready_i) begin
                            cm_state_d = CmMvSecondReg;
                          end
                        end
                        CmMvSecondReg: begin
                          // Move register indicated by r2s' into a1.
                          instr_o = cm_mva01s(.rs(instr_i[4:2]), .a01(1'b1));
                          if (id_in_ready_i) begin
                            // This is the final operation, so stop expanding and return to idle.
                            gets_expanded = INSTR_EXPANDED_LAST;
                            cm_state_d = CmIdle;
                          end
                        end
                        default: cm_state_d = CmIdle;
                      endcase
                    end
                    default: illegal_instr_o = 1'b1;
                  endcase
                end

                default: illegal_instr_o = 1'b1;
              endcase
            end else begin
              // The Zcmp extension is not enabled
              illegal_instr_o = 1'b1;
            end
          end

          3'b110: begin
            // c.swsp -> sw rs2, imm(x2)
            instr_o = {4'b0, instr_i[8:7], instr_i[12], instr_i[6:2], 5'h02, 3'b010,
                       instr_i[11:9], 2'b00, {OPCODE_STORE}};
          end

          3'b001,
          3'b011,
          3'b111: begin
            illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // Incoming instruction is not compressed.
      2'b11:;

      default: begin
        illegal_instr_o = 1'b1;
      end
    endcase
  end

  assign is_compressed_o = (instr_i[1:0] != 2'b11);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cm_state_q <= CmIdle;
    end else begin
      cm_state_q <= cm_state_d;
    end
  end

  if (ResetAll) begin : g_cm_meta_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cm_rlist_q     <= '0;
        cm_sp_offset_q <= '0;
      end else begin
        cm_rlist_q     <= cm_rlist_d;
        cm_sp_offset_q <= cm_sp_offset_d;
      end
    end
  end else begin : g_cm_meta_nr
    // The following regs don't need to be reset as they get assigned before first usage:
    always_ff @(posedge clk_i) begin
      cm_rlist_q     <= cm_rlist_d;
      cm_sp_offset_q <= cm_sp_offset_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // The valid_i signal used to gate below assertions must be known.
  `ASSERT_KNOWN(IbexInstrValidKnown, valid_i)

  // Selectors must be known/valid.
  `ASSERT(IbexInstrLSBsKnown, valid_i |->
      !$isunknown(instr_i[1:0]))
  `ASSERT(IbexC0Known1, (valid_i && (instr_i[1:0] == 2'b00)) |->
      !$isunknown(instr_i[15:13]))
  `ASSERT(IbexC1Known1, (valid_i && (instr_i[1:0] == 2'b01)) |->
      !$isunknown(instr_i[15:13]))
  `ASSERT(IbexC1Known2, (valid_i && (instr_i[1:0] == 2'b01) && (instr_i[15:13] == 3'b100)) |->
      !$isunknown(instr_i[11:10]))
  `ASSERT(IbexC1Known3, (valid_i &&
      (instr_i[1:0] == 2'b01) && (instr_i[15:13] == 3'b100) && (instr_i[11:10] == 2'b11)) |->
      !$isunknown({instr_i[12], instr_i[6:5]}))
  `ASSERT(IbexC2Known1, (valid_i && (instr_i[1:0] == 2'b10)) |->
      !$isunknown(instr_i[15:13]))
  `ASSERT(IbexPushPopFSMStable, !valid_i |-> cm_state_d == cm_state_q)

endmodule
