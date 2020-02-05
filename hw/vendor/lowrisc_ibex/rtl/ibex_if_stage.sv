// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Instruction Fetch Stage
 *
 * Instruction fetch unit: Selection of the next PC, and buffering (sampling) of
 * the read instruction.
 */

`include "prim_assert.sv"

module ibex_if_stage #(
    parameter int unsigned DmHaltAddr      = 32'h1A110800,
    parameter int unsigned DmExceptionAddr = 32'h1A110808
) (
    input  logic                   clk_i,
    input  logic                   rst_ni,

    input  logic [31:0]            boot_addr_i,              // also used for mtvec
    input  logic                   req_i,                    // instruction request control

    // instruction cache interface
    output logic                  instr_req_o,
    output logic [31:0]           instr_addr_o,
    input  logic                  instr_gnt_i,
    input  logic                  instr_rvalid_i,
    input  logic [31:0]           instr_rdata_i,
    input  logic                  instr_err_i,
    input  logic                  instr_pmp_err_i,

    // output of ID stage
    output logic                  instr_valid_id_o,         // instr in IF-ID is valid
    output logic                  instr_new_id_o,           // instr in IF-ID is new
    output logic [31:0]           instr_rdata_id_o,         // instr for ID stage
    output logic [31:0]           instr_rdata_alu_id_o,     // replicated instr for ID stage
                                                            // to reduce fan-out
    output logic [15:0]           instr_rdata_c_id_o,       // compressed instr for ID stage
                                                            // (mtval), meaningful only if
                                                            // instr_is_compressed_id_o = 1'b1
    output logic                  instr_is_compressed_id_o, // compressed decoder thinks this
                                                            // is a compressed instr
    output logic                  instr_fetch_err_o,        // bus error on fetch
    output logic                  illegal_c_insn_id_o,      // compressed decoder thinks this
                                                            // is an invalid instr
    output logic [31:0]           pc_if_o,
    output logic [31:0]           pc_id_o,

    // control signals
    input  logic                  instr_valid_clear_i,      // clear instr valid bit in IF-ID
    input  logic                  pc_set_i,                 // set the PC to a new value
    input  ibex_pkg::pc_sel_e     pc_mux_i,                 // selector for PC multiplexer
    input  ibex_pkg::exc_pc_sel_e exc_pc_mux_i,             // selects ISR address
    input  ibex_pkg::exc_cause_e  exc_cause,                // selects ISR address for
                                                            // vectorized interrupt lines
    // jump and branch target
    input  logic [31:0]           jump_target_ex_i,         // jump target address

    // CSRs
    input  logic [31:0]           csr_mepc_i,               // PC to restore after handling
                                                            // the interrupt/exception
    input  logic [31:0]           csr_depc_i,               // PC to restore after handling
                                                            // the debug request
    input  logic [31:0]           csr_mtvec_i,              // base PC to jump to on exception
    output logic                  csr_mtvec_init_o,         // tell CS regfile to init mtvec

    // pipeline stall
    input  logic                  id_in_ready_i,            // ID stage is ready for new instr

    // misc signals
    output logic                  if_busy_o,                // IF stage is busy fetching instr
    output logic                  perf_imiss_o              // instr fetch miss
);

  import ibex_pkg::*;

  logic              offset_in_init_d, offset_in_init_q;
  logic              have_instr;

  // prefetch buffer related signals
  logic              prefetch_busy;
  logic              branch_req;
  logic       [31:0] fetch_addr_n;

  logic              fetch_valid;
  logic              fetch_ready;
  logic       [31:0] fetch_rdata;
  logic       [31:0] fetch_addr;
  logic              fetch_err;

  logic       [31:0] exc_pc;

  logic        [5:0] irq_id;
  logic              unused_irq_bit;

  logic              if_id_pipe_reg_we; // IF-ID pipeline reg write enable

  logic        [7:0] unused_boot_addr;
  logic        [7:0] unused_csr_mtvec;

  assign unused_boot_addr = boot_addr_i[7:0];
  assign unused_csr_mtvec = csr_mtvec_i[7:0];

  // extract interrupt ID from exception cause
  assign irq_id         = {exc_cause};
  assign unused_irq_bit = irq_id[5];   // MSB distinguishes interrupts from exceptions

  // exception PC selection mux
  always_comb begin : exc_pc_mux
    unique case (exc_pc_mux_i)
      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                    };
      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_id[4:0], 2'b00 };
      EXC_PC_DBD:     exc_pc = DmHaltAddr;
      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;
      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                    };
    endcase
  end

  // fetch address selection mux
  always_comb begin : fetch_addr_mux
    unique case (pc_mux_i)
      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
      PC_JUMP: fetch_addr_n = jump_target_ex_i;
      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler
      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC
      PC_DRET: fetch_addr_n = csr_depc_i;
      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;

  // prefetch buffer, caches a fixed number of instructions
  ibex_prefetch_buffer prefetch_buffer_i (
      .clk_i             ( clk_i                       ),
      .rst_ni            ( rst_ni                      ),

      .req_i             ( req_i                       ),

      .branch_i          ( branch_req                  ),
      .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

      .ready_i           ( fetch_ready                 ),
      .valid_o           ( fetch_valid                 ),
      .rdata_o           ( fetch_rdata                 ),
      .addr_o            ( fetch_addr                  ),
      .err_o             ( fetch_err                   ),

      // goes to instruction memory / instruction cache
      .instr_req_o       ( instr_req_o                 ),
      .instr_addr_o      ( instr_addr_o                ),
      .instr_gnt_i       ( instr_gnt_i                 ),
      .instr_rvalid_i    ( instr_rvalid_i              ),
      .instr_rdata_i     ( instr_rdata_i               ),
      .instr_err_i       ( instr_err_i                 ),
      .instr_pmp_err_i   ( instr_pmp_err_i             ),

      // Prefetch Buffer Status
      .busy_o            ( prefetch_busy               )
  );


  // offset initialization state
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      offset_in_init_q <= 1'b1;
    end else begin
      offset_in_init_q <= offset_in_init_d;
    end
  end

  // offset initialization related transition logic
  always_comb begin
    offset_in_init_d = offset_in_init_q;

    fetch_ready      = 1'b0;
    branch_req       = 1'b0;
    have_instr       = 1'b0;

    if (offset_in_init_q) begin
      // no valid instruction data for ID stage, assume aligned
      if (req_i) begin
        branch_req       = 1'b1;
        offset_in_init_d = 1'b0;
      end
    end else begin
      // an instruction is ready for ID stage
      if (fetch_valid) begin
        have_instr = 1'b1;

        if (req_i && if_id_pipe_reg_we) begin
          fetch_ready      = 1'b1;
          offset_in_init_d = 1'b0;
        end
      end
    end

    // take care of jumps and branches
    if (pc_set_i) begin
      have_instr       = 1'b0;

      // switch to new PC from ID stage
      branch_req       = 1'b1;
      offset_in_init_d = 1'b0;
    end
  end

  assign pc_if_o      = fetch_addr;
  assign if_busy_o    = prefetch_busy;
  assign perf_imiss_o = ~fetch_valid | branch_req;

  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  logic [31:0] instr_decompressed;
  logic        illegal_c_insn;
  logic        instr_is_compressed_int;

  ibex_compressed_decoder compressed_decoder_i (
      .clk_i           ( clk_i                   ),
      .rst_ni          ( rst_ni                  ),
      .valid_i         ( fetch_valid             ),
      .instr_i         ( fetch_rdata             ),
      .instr_o         ( instr_decompressed      ),
      .is_compressed_o ( instr_is_compressed_int ),
      .illegal_instr_o ( illegal_c_insn          )
  );

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  assign if_id_pipe_reg_we = have_instr & id_in_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin : if_id_pipeline_regs
    if (!rst_ni) begin
      instr_new_id_o             <= 1'b0;
      instr_valid_id_o           <= 1'b0;
      instr_rdata_id_o           <= '0;
      instr_rdata_alu_id_o       <= '0;
      instr_fetch_err_o          <= '0;
      instr_rdata_c_id_o         <= '0;
      instr_is_compressed_id_o   <= 1'b0;
      illegal_c_insn_id_o        <= 1'b0;
      pc_id_o                    <= '0;
    end else begin
      instr_new_id_o             <= if_id_pipe_reg_we;
      if (if_id_pipe_reg_we) begin
        instr_valid_id_o         <= 1'b1;
        instr_rdata_id_o         <= instr_decompressed;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_decompressed;
        instr_fetch_err_o        <= fetch_err;
        instr_rdata_c_id_o       <= fetch_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_int;
        illegal_c_insn_id_o      <= illegal_c_insn;
        pc_id_o                  <= pc_if_o;
      end else if (instr_valid_clear_i) begin
        instr_valid_id_o         <= 1'b0;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN(IbexExcPcMuxKnown, exc_pc_mux_i, clk_i, !rst_ni)
  `ASSERT(IbexPcMuxValid, pc_mux_i inside {
      PC_BOOT,
      PC_JUMP,
      PC_EXC,
      PC_ERET,
      PC_DRET
      }, clk_i, !rst_ni)

  // Boot address must be aligned to 256 bytes.
  `ASSERT(IbexBootAddrUnaligned, boot_addr_i[7:0] == 8'h00, clk_i, !rst_ni)

  // Errors must only be sent together with rvalid.
  `ASSERT(IbexInstrErrWithoutRvalid, instr_err_i |-> instr_rvalid_i, clk_i, !rst_ni)

  // Address must not contain X when request is sent.
  `ASSERT(IbexInstrAddrUnknown, instr_req_o |-> !$isunknown(instr_addr_o), clk_i, !rst_ni)

  // Address must be word aligned when request is sent.
  `ASSERT(IbexInstrAddrUnaligned, instr_req_o |-> (instr_addr_o[1:0] == 2'b00), clk_i, !rst_ni)

endmodule
