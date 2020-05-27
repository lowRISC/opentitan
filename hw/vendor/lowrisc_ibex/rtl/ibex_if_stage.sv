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
    parameter int unsigned DmHaltAddr        = 32'h1A110800,
    parameter int unsigned DmExceptionAddr   = 32'h1A110808,
    parameter bit          DummyInstructions = 1'b0,
    parameter bit          ICache            = 1'b0,
    parameter bit          ICacheECC         = 1'b0
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
    output logic                  instr_fetch_err_plus2_o,  // bus error misaligned
    output logic                  illegal_c_insn_id_o,      // compressed decoder thinks this
                                                            // is an invalid instr
    output logic                  dummy_instr_id_o,         // Instruction is a dummy
    output logic [31:0]           pc_if_o,
    output logic [31:0]           pc_id_o,

    // control signals
    input  logic                  instr_valid_clear_i,      // clear instr valid bit in IF-ID
    input  logic                  pc_set_i,                 // set the PC to a new value
    input  logic                  pc_set_spec_i,
    input  ibex_pkg::pc_sel_e     pc_mux_i,                 // selector for PC multiplexer
    input  ibex_pkg::exc_pc_sel_e exc_pc_mux_i,             // selects ISR address
    input  ibex_pkg::exc_cause_e  exc_cause,                // selects ISR address for
                                                            // vectorized interrupt lines
    input logic                   dummy_instr_en_i,
    input logic [2:0]             dummy_instr_mask_i,
    input logic                   dummy_instr_seed_en_i,
    input logic [31:0]            dummy_instr_seed_i,
    input logic                   icache_enable_i,
    input logic                   icache_inval_i,

    // jump and branch target
    input  logic [31:0]           branch_target_ex_i,       // branch/jump target address

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
    output logic                  if_busy_o                 // IF stage is busy fetching instr
);

  import ibex_pkg::*;

  logic              instr_valid_id_d, instr_valid_id_q;
  logic              instr_new_id_d, instr_new_id_q;

  // prefetch buffer related signals
  logic              prefetch_busy;
  logic              branch_req;
  logic       [31:0] fetch_addr_n;

  logic              fetch_valid;
  logic              fetch_ready;
  logic       [31:0] fetch_rdata;
  logic       [31:0] fetch_addr;
  logic              fetch_err;
  logic              fetch_err_plus2;

  logic       [31:0] exc_pc;

  logic        [5:0] irq_id;
  logic              unused_irq_bit;

  logic              if_id_pipe_reg_we; // IF-ID pipeline reg write enable

  // Dummy instruction signals
  logic              fetch_valid_out;
  logic              stall_dummy_instr;
  logic [31:0]       instr_out;
  logic              instr_is_compressed_out;
  logic              illegal_c_instr_out;
  logic              instr_err_out;

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
      PC_JUMP: fetch_addr_n = branch_target_ex_i;
      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler
      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC
      PC_DRET: fetch_addr_n = csr_depc_i;
      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;

  if (ICache) begin : gen_icache
    // Full I-Cache option
    ibex_icache #(
      .ICacheECC (ICacheECC)
    ) icache_i (
        .clk_i             ( clk_i                       ),
        .rst_ni            ( rst_ni                      ),

        .req_i             ( req_i                       ),

        .branch_i          ( branch_req                  ),
        .branch_spec_i     ( pc_set_spec_i               ),
        .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

        .ready_i           ( fetch_ready                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( fetch_rdata                 ),
        .addr_o            ( fetch_addr                  ),
        .err_o             ( fetch_err                   ),
        .err_plus2_o       ( fetch_err_plus2             ),

        .instr_req_o       ( instr_req_o                 ),
        .instr_addr_o      ( instr_addr_o                ),
        .instr_gnt_i       ( instr_gnt_i                 ),
        .instr_rvalid_i    ( instr_rvalid_i              ),
        .instr_rdata_i     ( instr_rdata_i               ),
        .instr_err_i       ( instr_err_i                 ),
        .instr_pmp_err_i   ( instr_pmp_err_i             ),

        .icache_enable_i   ( icache_enable_i             ),
        .icache_inval_i    ( icache_inval_i              ),
        .busy_o            ( prefetch_busy               )
    );
  end else begin : gen_prefetch_buffer
    // prefetch buffer, caches a fixed number of instructions
    ibex_prefetch_buffer prefetch_buffer_i (
        .clk_i             ( clk_i                       ),
        .rst_ni            ( rst_ni                      ),

        .req_i             ( req_i                       ),

        .branch_i          ( branch_req                  ),
        .branch_spec_i     ( pc_set_spec_i               ),
        .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

        .ready_i           ( fetch_ready                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( fetch_rdata                 ),
        .addr_o            ( fetch_addr                  ),
        .err_o             ( fetch_err                   ),
        .err_plus2_o       ( fetch_err_plus2             ),

        .instr_req_o       ( instr_req_o                 ),
        .instr_addr_o      ( instr_addr_o                ),
        .instr_gnt_i       ( instr_gnt_i                 ),
        .instr_rvalid_i    ( instr_rvalid_i              ),
        .instr_rdata_i     ( instr_rdata_i               ),
        .instr_err_i       ( instr_err_i                 ),
        .instr_pmp_err_i   ( instr_pmp_err_i             ),

        .busy_o            ( prefetch_busy               )
    );
    // ICache tieoffs
    logic unused_icen, unused_icinv;
    assign unused_icen  = icache_enable_i;
    assign unused_icinv = icache_inval_i;
  end

  assign branch_req  = pc_set_i;
  assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;

  assign pc_if_o     = fetch_addr;
  assign if_busy_o   = prefetch_busy;

  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  logic [31:0] instr_decompressed;
  logic        illegal_c_insn;
  logic        instr_is_compressed;

  ibex_compressed_decoder compressed_decoder_i (
      .clk_i           ( clk_i                    ),
      .rst_ni          ( rst_ni                   ),
      .valid_i         ( fetch_valid & ~fetch_err ),
      .instr_i         ( fetch_rdata              ),
      .instr_o         ( instr_decompressed       ),
      .is_compressed_o ( instr_is_compressed      ),
      .illegal_instr_o ( illegal_c_insn           )
  );

  // Dummy instruction insertion
  if (DummyInstructions) begin : gen_dummy_instr
    logic        insert_dummy_instr;
    logic [31:0] dummy_instr_data;

    ibex_dummy_instr dummy_instr_i (
      .clk_i                 ( clk_i                 ),
      .rst_ni                ( rst_ni                ),
      .dummy_instr_en_i      ( dummy_instr_en_i      ),
      .dummy_instr_mask_i    ( dummy_instr_mask_i    ),
      .dummy_instr_seed_en_i ( dummy_instr_seed_en_i ),
      .dummy_instr_seed_i    ( dummy_instr_seed_i    ),
      .fetch_valid_i         ( fetch_valid           ),
      .id_in_ready_i         ( id_in_ready_i         ),
      .insert_dummy_instr_o  ( insert_dummy_instr    ),
      .dummy_instr_data_o    ( dummy_instr_data      )
    );

    // Mux between actual instructions and dummy instructions
    assign fetch_valid_out         = insert_dummy_instr | fetch_valid;
    assign instr_out               = insert_dummy_instr ? dummy_instr_data : instr_decompressed;
    assign instr_is_compressed_out = insert_dummy_instr ? 1'b0 : instr_is_compressed;
    assign illegal_c_instr_out     = insert_dummy_instr ? 1'b0 : illegal_c_insn;
    assign instr_err_out           = insert_dummy_instr ? 1'b0 : fetch_err;

    // Stall the IF stage if we insert a dummy instruction. The dummy will execute between whatever
    // is currently in the ID stage and whatever is valid from the prefetch buffer this cycle. The
    // PC of the dummy instruction will match whatever is next from the prefetch buffer.
    assign stall_dummy_instr = insert_dummy_instr;

    // Register the dummy instruction indication into the ID stage
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        dummy_instr_id_o <= 1'b0;
      end else if (if_id_pipe_reg_we) begin
        dummy_instr_id_o <= insert_dummy_instr;
      end
    end

  end else begin : gen_no_dummy_instr
    logic        unused_dummy_en;
    logic [2:0]  unused_dummy_mask;
    logic        unused_dummy_seed_en;
    logic [31:0] unused_dummy_seed;

    assign unused_dummy_en         = dummy_instr_en_i;
    assign unused_dummy_mask       = dummy_instr_mask_i;
    assign unused_dummy_seed_en    = dummy_instr_seed_en_i;
    assign unused_dummy_seed       = dummy_instr_seed_i;
    assign fetch_valid_out         = fetch_valid;
    assign instr_out               = instr_decompressed;
    assign instr_is_compressed_out = instr_is_compressed;
    assign illegal_c_instr_out     = illegal_c_insn;
    assign instr_err_out           = fetch_err;
    assign stall_dummy_instr       = 1'b0;
    assign dummy_instr_id_o        = 1'b0;
  end

  // The ID stage becomes valid as soon as any instruction is registered in the ID stage flops.
  // Note that the current instruction is squashed by the incoming pc_set_i signal.
  // Valid is held until it is explicitly cleared (due to an instruction completing or an exception)
  assign instr_valid_id_d = (fetch_valid_out & id_in_ready_i & ~pc_set_i) |
                            (instr_valid_id_q & ~instr_valid_clear_i);
  assign instr_new_id_d   = fetch_valid_out & id_in_ready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_valid_id_q <= 1'b0;
      instr_new_id_q   <= 1'b0;
    end else begin
      instr_valid_id_q <= instr_valid_id_d;
      instr_new_id_q   <= instr_new_id_d;
    end
  end

  assign instr_valid_id_o = instr_valid_id_q;
  // Signal when a new instruction enters the ID stage (only used for RVFI signalling).
  assign instr_new_id_o   = instr_new_id_q;

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  assign if_id_pipe_reg_we = instr_new_id_d;

  always_ff @(posedge clk_i) begin
    if (if_id_pipe_reg_we) begin
      instr_rdata_id_o         <= instr_out;
      // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
      instr_rdata_alu_id_o     <= instr_out;
      instr_fetch_err_o        <= instr_err_out;
      instr_fetch_err_plus2_o  <= fetch_err_plus2;
      instr_rdata_c_id_o       <= fetch_rdata[15:0];
      instr_is_compressed_id_o <= instr_is_compressed_out;
      illegal_c_insn_id_o      <= illegal_c_instr_out;
      pc_id_o                  <= pc_if_o;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN(IbexExcPcMuxKnown, exc_pc_mux_i)
  `ASSERT(IbexPcMuxValid, pc_mux_i inside {
      PC_BOOT,
      PC_JUMP,
      PC_EXC,
      PC_ERET,
      PC_DRET})

  // Boot address must be aligned to 256 bytes.
  `ASSERT(IbexBootAddrUnaligned, boot_addr_i[7:0] == 8'h00)

  // Errors must only be sent together with rvalid.
  `ASSERT(IbexInstrErrWithoutRvalid, instr_err_i |-> instr_rvalid_i)

  // Address must not contain X when request is sent.
  `ASSERT(IbexInstrAddrUnknown, instr_req_o |-> !$isunknown(instr_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexInstrAddrUnaligned, instr_req_o |-> (instr_addr_o[1:0] == 2'b00))

endmodule
