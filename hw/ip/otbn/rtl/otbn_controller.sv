// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN Controller
 */
module otbn_controller
  import otbn_pkg::*;
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic                     start_i, // start the processing at start_addr_i
  output logic                     done_o,  // processing done, signaled by ECALL
  input  logic [ImemAddrWidth-1:0] start_addr_i,

  // Next instruction selection (to instruction fetch)
  output logic                     insn_fetch_req_valid_o,
  output logic [ImemAddrWidth-1:0] insn_fetch_req_addr_o,

  // Fetched/decoded instruction
  input  logic                     insn_valid_i,
  input  logic [ImemAddrWidth-1:0] insn_addr_i,

  // Decoded instruction data, matching the "Decoding" section of the specification.
  input insn_dec_base_t       insn_dec_base_i,
  input insn_dec_ctrl_t       insn_dec_ctrl_i,

  // Base register file
  output logic [4:0]   rf_base_wr_addr_o,
  output logic         rf_base_wr_en_o,
  output logic [31:0]  rf_base_wr_data_o,

  output logic [4:0]   rf_base_rd_addr_a_o,
  input  logic [31:0]  rf_base_rd_data_a_i,

  output logic [4:0]   rf_base_rd_addr_b_o,
  input  logic [31:0]  rf_base_rd_data_b_i,

  // Execution units
  output alu_base_operation_t  alu_base_operation_o,
  output alu_base_comparison_t alu_base_comparison_o,
  input  logic [31:0]          alu_base_operation_result_i,
  input  logic                 alu_base_comparison_result_i,

  output logic                     lsu_load_req_o,
  output logic                     lsu_store_req_o,
  output insn_subset_e             lsu_req_subset_o,
  output logic [DmemAddrWidth-1:0] lsu_addr_o,

  output logic [31:0]              lsu_base_wdata_o,
  output logic [WLEN-1:0]          lsu_bignum_wdata_o,

  input  logic [31:0]              lsu_base_rdata_i,
  input  logic [WLEN-1:0]          lsu_bignum_rdata_i,
  input  logic [1:0]               lsu_rdata_err_i // Bit1: Uncorrectable, Bit0: Correctable
);

  typedef enum logic [1:0] {
    OtbnStateHalt,
    OtbnStateRun,
    OtbnStateStall
  } otbn_state_e;

  otbn_state_e state_q, state_d;

  logic stall;
  logic mem_stall;
  logic branch_taken;
  logic [ImemAddrWidth-1:0] branch_target;
  logic [ImemAddrWidth-1:0] next_insn_addr;

  // Stall a cycle on loads to allow load data writeback to happen the following cycle. Stall not
  // required on stores as there is no response to deal with.
  // TODO: Possibility of error response on store? Probably still don't need to stall in that case
  // just ensure incoming store error stops anything else happening.
  assign mem_stall = lsu_load_req_o;

  assign stall = mem_stall;
  assign done_o = insn_valid_i && insn_dec_ctrl_i.ecall_insn;

  // Branch taken when there is a valid branch instruction and comparison passes or a valid jump
  // instruction (which is always taken)
  assign branch_taken = insn_valid_i & ((insn_dec_ctrl_i.branch_insn & alu_base_comparison_result_i) |
                                        insn_dec_ctrl_i.jump_insn);
  // Branch target computed by base ALU (PC + imm)
  // TODO: Implement error on branch out of range
  assign branch_target = alu_base_operation_result_i[ImemAddrWidth-1:0];

  assign next_insn_addr = insn_addr_i + 'd4;

  always_comb begin
    state_d                = state_q;
    insn_fetch_req_valid_o = 1'b0;
    insn_fetch_req_addr_o  = start_addr_i;

    // TODO: Harden state machine
    // TODO: Jumps/branches
    unique case (state_q)
      OtbnStateHalt: begin
        if (start_i) begin
          state_d = OtbnStateRun;
          insn_fetch_req_addr_o  = start_addr_i;
          insn_fetch_req_valid_o = 1'b01;
        end
      end
      OtbnStateRun: begin
        insn_fetch_req_valid_o = 1'b1;

        if (done_o) begin
          state_d                = OtbnStateHalt;
          insn_fetch_req_valid_o = 1'b0;
        end else begin
          // When stalling refetch the same instruction to keep decode inputs constant
          if (stall) begin
            state_d               = OtbnStateStall;
            insn_fetch_req_addr_o = insn_addr_i;
          end else begin
            if (branch_taken) begin
              insn_fetch_req_addr_o = branch_target;
            end else begin
              insn_fetch_req_addr_o = next_insn_addr;
            end
          end
        end
      end
      OtbnStateStall: begin
        // Only ever stall for a single cycle
        // TODO: Any more than one cycle stall cases?
        insn_fetch_req_valid_o = 1'b1;
        insn_fetch_req_addr_o  = next_insn_addr;
        state_d = OtbnStateRun;
      end
      default: ;
    endcase
  end

  `ASSERT(ControllerStateValid, state_q inside {OtbnStateHalt, OtbnStateRun, OtbnStateStall});
  // Branch only takes effect in OtbnStateRun so must not go into stall state for branch
  // instructions.
  `ASSERT(NoStallOnBranch, insn_valid_i & insn_dec_ctrl_i.branch_insn |-> state_q != OtbnStateStall);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= OtbnStateHalt;
    end else begin
      state_q <= state_d;
    end
  end

  assign rf_base_rd_addr_a_o = insn_dec_base_i.a;
  assign rf_base_rd_addr_b_o = insn_dec_base_i.b;

  // Base ALU Operand A MUX
  always_comb begin
    unique case (insn_dec_ctrl_i.op_a_sel)
      OpASelRegister:
        alu_base_operation_o.operand_a = rf_base_rd_data_a_i;
      OpASelZero:
        alu_base_operation_o.operand_a = '0;
      OpASelCurrPc:
        alu_base_operation_o.operand_a = {{(32 - ImemAddrWidth){1'b0}}, insn_addr_i};
      default:
        alu_base_operation_o.operand_a = rf_base_rd_data_a_i;
    endcase
  end

  // Base ALU Operand B MUX
  always_comb begin
    unique case (insn_dec_ctrl_i.op_b_sel)
      OpBSelRegister:
        alu_base_operation_o.operand_b = rf_base_rd_data_b_i;
      OpBSelImmediate:
        alu_base_operation_o.operand_b = insn_dec_base_i.i;
      default:
        alu_base_operation_o.operand_b = rf_base_rd_data_b_i;
    endcase
  end

  assign alu_base_operation_o.op = insn_dec_base_i.alu_op;

  assign alu_base_comparison_o.operand_a = rf_base_rd_data_a_i;
  assign alu_base_comparison_o.operand_b = rf_base_rd_data_b_i;
  assign alu_base_comparison_o.op = insn_dec_base_i.comparison_op;

  // Register file write MUX
  // Suppress write for loads when controller isn't in stall state as load data for writeback is
  // only available in the stall state.
  assign rf_base_wr_en_o =
   insn_dec_ctrl_i.rf_we & ~(insn_dec_ctrl_i.ld_insn & (state_q != OtbnStateStall));

  assign rf_base_wr_addr_o = insn_dec_base_i.d;

  always_comb begin
    unique case (insn_dec_ctrl_i.rf_wdata_sel)
      RfWdSelEx:
        rf_base_wr_data_o = alu_base_operation_result_i;
      RfWdSelLsu:
        rf_base_wr_data_o = lsu_base_rdata_i;
      RfWdSelNextPc:
        rf_base_wr_data_o = {{(32-ImemAddrWidth){1'b0}}, next_insn_addr};
      default:
        rf_base_wr_data_o = alu_base_operation_result_i;
    endcase
  end

  // TODO: Add error on unaligned/out of bounds
  assign lsu_load_req_o   = insn_valid_i & insn_dec_ctrl_i.ld_insn & (state_q == OtbnStateRun);
  assign lsu_store_req_o  = insn_valid_i & insn_dec_ctrl_i.st_insn & (state_q == OtbnStateRun);
  assign lsu_req_subset_o = insn_dec_ctrl_i.subset;
  // TODO: Switch between address from base/bignum
  assign lsu_addr_o       = alu_base_operation_result_i[DmemAddrWidth-1:0];
  assign lsu_base_wdata_o = rf_base_rd_data_b_i;

  // TODO: Bignum load/store
  assign lsu_bignum_wdata_o = '0;
endmodule
