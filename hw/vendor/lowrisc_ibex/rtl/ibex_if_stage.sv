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

module ibex_if_stage import ibex_pkg::*; #(
  parameter int unsigned DmHaltAddr        = 32'h1A110800,
  parameter int unsigned DmExceptionAddr   = 32'h1A110808,
  parameter bit          DummyInstructions = 1'b0,
  parameter bit          ICache            = 1'b0,
  parameter bit          ICacheECC         = 1'b0,
  parameter int unsigned BusSizeECC        = BUS_SIZE,
  parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
  parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
  parameter bit          PCIncrCheck       = 1'b0,
  parameter bit          ResetAll          = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed   = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm   = RndCnstLfsrPermDefault,
  parameter bit          BranchPredictor   = 1'b0,
  parameter bit          MemECC            = 1'b0,
  parameter int unsigned MemDataWidth      = MemECC ? 32 + 7 : 32
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  boot_addr_i,              // also used for mtvec
  input  logic                         req_i,                    // instruction request control

  // instruction cache interface
  output logic                        instr_req_o,
  output logic [31:0]                 instr_addr_o,
  input  logic                        instr_gnt_i,
  input  logic                        instr_rvalid_i,
  input  logic [MemDataWidth-1:0]     instr_rdata_i,
  input  logic                        instr_bus_err_i,
  output logic                        instr_intg_err_o,

  // ICache RAM IO
  output logic [IC_NUM_WAYS-1:0]      ic_tag_req_o,
  output logic                        ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]       ic_tag_addr_o,
  output logic [TagSizeECC-1:0]       ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]       ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]      ic_data_req_o,
  output logic                        ic_data_write_o,
  output logic [IC_INDEX_W-1:0]       ic_data_addr_o,
  output logic [LineSizeECC-1:0]      ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]      ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                        ic_scr_key_valid_i,
  output logic                        ic_scr_key_req_o,

  // output of ID stage
  output logic                        instr_valid_id_o,         // instr in IF-ID is valid
  output logic                        instr_new_id_o,           // instr in IF-ID is new
  output logic [31:0]                 instr_rdata_id_o,         // instr for ID stage
  output logic [31:0]                 instr_rdata_alu_id_o,     // replicated instr for ID stage
                                                                // to reduce fan-out
  output logic [15:0]                 instr_rdata_c_id_o,       // compressed instr for ID stage
                                                                // (mtval), meaningful only if
                                                                // instr_is_compressed_id_o = 1'b1
  output logic                        instr_is_compressed_id_o, // compressed decoder thinks this
                                                                // is a compressed instr
  output logic                        instr_bp_taken_o,         // instruction was predicted to be
                                                                // a taken branch
  output logic                        instr_fetch_err_o,        // bus error on fetch
  output logic                        instr_fetch_err_plus2_o,  // bus error misaligned
  output logic                        illegal_c_insn_id_o,      // compressed decoder thinks this
                                                                // is an invalid instr
  output logic                        dummy_instr_id_o,         // Instruction is a dummy
  output logic [31:0]                 pc_if_o,
  output logic [31:0]                 pc_id_o,
  input  logic                        pmp_err_if_i,
  input  logic                        pmp_err_if_plus2_i,

  // control signals
  input  logic                        instr_valid_clear_i,      // clear instr valid bit in IF-ID
  input  logic                        pc_set_i,                 // set the PC to a new value
  input  pc_sel_e                     pc_mux_i,                 // selector for PC multiplexer
  input  logic                        nt_branch_mispredict_i,   // Not-taken branch in ID/EX was
                                                                // mispredicted (predicted taken)
  input  logic [31:0]                 nt_branch_addr_i,         // Not-taken branch address in ID/EX
  input  exc_pc_sel_e                 exc_pc_mux_i,             // selects ISR address
  input  exc_cause_t                  exc_cause,                // selects ISR address for
                                                                // vectorized interrupt lines
  input  logic                        dummy_instr_en_i,
  input  logic [2:0]                  dummy_instr_mask_i,
  input  logic                        dummy_instr_seed_en_i,
  input  logic [31:0]                 dummy_instr_seed_i,
  input  logic                        icache_enable_i,
  input  logic                        icache_inval_i,
  output logic                        icache_ecc_error_o,

  // jump and branch target
  input  logic [31:0]                 branch_target_ex_i,       // branch/jump target address

  // CSRs
  input  logic [31:0]                 csr_mepc_i,               // PC to restore after handling
                                                                // the interrupt/exception
  input  logic [31:0]                 csr_depc_i,               // PC to restore after handling
                                                                // the debug request
  input  logic [31:0]                 csr_mtvec_i,              // base PC to jump to on exception
  output logic                        csr_mtvec_init_o,         // tell CS regfile to init mtvec

  // pipeline stall
  input  logic                        id_in_ready_i,            // ID stage is ready for new instr

  // misc signals
  output logic                        pc_mismatch_alert_o,
  output logic                        if_busy_o                 // IF stage is busy fetching instr
);

  logic              instr_valid_id_d, instr_valid_id_q;
  logic              instr_new_id_d, instr_new_id_q;

  logic              instr_err, instr_intg_err;

  // prefetch buffer related signals
  logic              prefetch_busy;
  logic              branch_req;
  logic       [31:0] fetch_addr_n;
  logic              unused_fetch_addr_n0;

  logic              prefetch_branch;
  logic [31:0]       prefetch_addr;

  logic              fetch_valid_raw;
  logic              fetch_valid;
  logic              fetch_ready;
  logic       [31:0] fetch_rdata;
  logic       [31:0] fetch_addr;
  logic              fetch_err;
  logic              fetch_err_plus2;

  logic [31:0]       instr_decompressed;
  logic              illegal_c_insn;
  logic              instr_is_compressed;

  logic              if_instr_valid;
  logic       [31:0] if_instr_rdata;
  logic       [31:0] if_instr_addr;
  logic              if_instr_bus_err;
  logic              if_instr_pmp_err;
  logic              if_instr_err;
  logic              if_instr_err_plus2;

  logic       [31:0] exc_pc;

  logic              if_id_pipe_reg_we; // IF-ID pipeline reg write enable

  // Dummy instruction signals
  logic              stall_dummy_instr;
  logic [31:0]       instr_out;
  logic              instr_is_compressed_out;
  logic              illegal_c_instr_out;
  logic              instr_err_out;

  logic              predict_branch_taken;
  logic       [31:0] predict_branch_pc;

  logic        [4:0] irq_vec;

  ibex_pkg::pc_sel_e pc_mux_internal;

  logic        [7:0] unused_boot_addr;
  logic        [7:0] unused_csr_mtvec;
  logic              unused_exc_cause;

  assign unused_boot_addr = boot_addr_i[7:0];
  assign unused_csr_mtvec = csr_mtvec_i[7:0];

  assign unused_exc_cause = |{exc_cause.irq_ext, exc_cause.irq_int};

  // exception PC selection mux
  always_comb begin : exc_pc_mux
    irq_vec = exc_cause.lower_cause;

    if (exc_cause.irq_int) begin
      // All internal interrupts go to the NMI vector
      irq_vec = ExcCauseIrqNm.lower_cause;
    end

    unique case (exc_pc_mux_i)
      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                };
      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };
      EXC_PC_DBD:     exc_pc = DmHaltAddr;
      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;
      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                };
    endcase
  end

  // The Branch predictor can provide a new PC which is internal to if_stage. Only override the mux
  // select to choose this if the core isn't already trying to set a PC.
  assign pc_mux_internal =
    (BranchPredictor && predict_branch_taken && !pc_set_i) ? PC_BP : pc_mux_i;

  // fetch address selection mux
  always_comb begin : fetch_addr_mux
    unique case (pc_mux_internal)
      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
      PC_JUMP: fetch_addr_n = branch_target_ex_i;
      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler
      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC
      PC_DRET: fetch_addr_n = csr_depc_i;
      // Without branch predictor will never get pc_mux_internal == PC_BP. We still handle no branch
      // predictor case here to ensure redundant mux logic isn't synthesised.
      PC_BP:   fetch_addr_n = BranchPredictor ? predict_branch_pc : { boot_addr_i[31:8], 8'h80 };
      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };
    endcase
  end

  // tell CS register file to initialize mtvec on boot
  assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;

  // SEC_CM: BUS.INTEGRITY
  if (MemECC) begin : g_mem_ecc
    logic [1:0] ecc_err;
    logic [MemDataWidth-1:0] instr_rdata_buf;

    prim_buf #(.Width(MemDataWidth)) u_prim_buf_instr_rdata (
      .in_i (instr_rdata_i),
      .out_o(instr_rdata_buf)
    );

    prim_secded_inv_39_32_dec u_instr_intg_dec (
      .data_i     (instr_rdata_buf),
      .data_o     (),
      .syndrome_o (),
      .err_o      (ecc_err)
    );

    // Don't care if error is correctable or not, they're all treated the same
    assign instr_intg_err = |ecc_err;
  end else begin : g_no_mem_ecc
    assign instr_intg_err            = 1'b0;
  end

  assign instr_err        = instr_intg_err | instr_bus_err_i;
  assign instr_intg_err_o = instr_intg_err & instr_rvalid_i;

  // There are two possible "branch please" signals that are computed in the IF stage: branch_req
  // and nt_branch_mispredict_i. These should be mutually exclusive (see the NoMispredBranch
  // assertion), so we can just OR the signals together.
  assign prefetch_branch = branch_req | nt_branch_mispredict_i;
  assign prefetch_addr   = branch_req ? {fetch_addr_n[31:1], 1'b0} : nt_branch_addr_i;

  // The fetch_valid signal that comes out of the icache or prefetch buffer should be squashed if we
  // had a misprediction.
  assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i;

  // We should never see a mispredict and an incoming branch on the same cycle. The mispredict also
  // cancels any predicted branch so overall branch_req must be low.
  `ASSERT(NoMispredBranch, nt_branch_mispredict_i |-> ~branch_req)

  if (ICache) begin : gen_icache
    // Full I-Cache option
    ibex_icache #(
      .ICacheECC       (ICacheECC),
      .ResetAll        (ResetAll),
      .BusSizeECC      (BusSizeECC),
      .TagSizeECC      (TagSizeECC),
      .LineSizeECC     (LineSizeECC)
    ) icache_i (
        .clk_i               ( clk_i                      ),
        .rst_ni              ( rst_ni                     ),

        .req_i               ( req_i                      ),

        .branch_i            ( prefetch_branch            ),
        .addr_i              ( prefetch_addr              ),

        .ready_i             ( fetch_ready                ),
        .valid_o             ( fetch_valid_raw            ),
        .rdata_o             ( fetch_rdata                ),
        .addr_o              ( fetch_addr                 ),
        .err_o               ( fetch_err                  ),
        .err_plus2_o         ( fetch_err_plus2            ),

        .instr_req_o         ( instr_req_o                ),
        .instr_addr_o        ( instr_addr_o               ),
        .instr_gnt_i         ( instr_gnt_i                ),
        .instr_rvalid_i      ( instr_rvalid_i             ),
        .instr_rdata_i       ( instr_rdata_i[31:0]        ),
        .instr_err_i         ( instr_err                  ),

        .ic_tag_req_o        ( ic_tag_req_o               ),
        .ic_tag_write_o      ( ic_tag_write_o             ),
        .ic_tag_addr_o       ( ic_tag_addr_o              ),
        .ic_tag_wdata_o      ( ic_tag_wdata_o             ),
        .ic_tag_rdata_i      ( ic_tag_rdata_i             ),
        .ic_data_req_o       ( ic_data_req_o              ),
        .ic_data_write_o     ( ic_data_write_o            ),
        .ic_data_addr_o      ( ic_data_addr_o             ),
        .ic_data_wdata_o     ( ic_data_wdata_o            ),
        .ic_data_rdata_i     ( ic_data_rdata_i            ),
        .ic_scr_key_valid_i  ( ic_scr_key_valid_i         ),
        .ic_scr_key_req_o    ( ic_scr_key_req_o           ),

        .icache_enable_i     ( icache_enable_i            ),
        .icache_inval_i      ( icache_inval_i             ),
        .busy_o              ( prefetch_busy              ),
        .ecc_error_o         ( icache_ecc_error_o         )
    );
  end else begin : gen_prefetch_buffer
    // prefetch buffer, caches a fixed number of instructions
    ibex_prefetch_buffer #(
      .ResetAll        (ResetAll)
    ) prefetch_buffer_i (
        .clk_i               ( clk_i                      ),
        .rst_ni              ( rst_ni                     ),

        .req_i               ( req_i                      ),

        .branch_i            ( prefetch_branch            ),
        .addr_i              ( prefetch_addr              ),

        .ready_i             ( fetch_ready                ),
        .valid_o             ( fetch_valid_raw            ),
        .rdata_o             ( fetch_rdata                ),
        .addr_o              ( fetch_addr                 ),
        .err_o               ( fetch_err                  ),
        .err_plus2_o         ( fetch_err_plus2            ),

        .instr_req_o         ( instr_req_o                ),
        .instr_addr_o        ( instr_addr_o               ),
        .instr_gnt_i         ( instr_gnt_i                ),
        .instr_rvalid_i      ( instr_rvalid_i             ),
        .instr_rdata_i       ( instr_rdata_i[31:0]        ),
        .instr_err_i         ( instr_err                  ),

        .busy_o              ( prefetch_busy              )
    );
    // ICache tieoffs
    logic                   unused_icen, unused_icinv, unused_scr_key_valid;
    logic [TagSizeECC-1:0]  unused_tag_ram_input [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] unused_data_ram_input [IC_NUM_WAYS];
    assign unused_icen           = icache_enable_i;
    assign unused_icinv          = icache_inval_i;
    assign unused_tag_ram_input  = ic_tag_rdata_i;
    assign unused_data_ram_input = ic_data_rdata_i;
    assign unused_scr_key_valid  = ic_scr_key_valid_i;
    assign ic_tag_req_o          = 'b0;
    assign ic_tag_write_o        = 'b0;
    assign ic_tag_addr_o         = 'b0;
    assign ic_tag_wdata_o        = 'b0;
    assign ic_data_req_o         = 'b0;
    assign ic_data_write_o       = 'b0;
    assign ic_data_addr_o        = 'b0;
    assign ic_data_wdata_o       = 'b0;
    assign ic_scr_key_req_o      = 'b0;
    assign icache_ecc_error_o    = 'b0;

`ifndef SYNTHESIS
    // If we don't instantiate an icache and this is a simulation then we have a problem because the
    // simulator might discard the icache module entirely, including some DPI exports that it
    // implies. This then causes problems for linking against C++ testbench code that expected them.
    // As a slightly ugly hack, let's define the DPI functions here (the real versions are defined
    // in prim_util_get_scramble_params.svh)
    export "DPI-C" function simutil_get_scramble_key;
    export "DPI-C" function simutil_get_scramble_nonce;
    function automatic int simutil_get_scramble_key(output bit [127:0] val);
      return 0;
    endfunction
    function automatic int simutil_get_scramble_nonce(output bit [319:0] nonce);
      return 0;
    endfunction
`endif
  end

  assign unused_fetch_addr_n0 = fetch_addr_n[0];

  assign branch_req  = pc_set_i | predict_branch_taken;

  assign pc_if_o     = if_instr_addr;
  assign if_busy_o   = prefetch_busy;

  // PMP errors
  // An error can come from the instruction address, or the next instruction address for unaligned,
  // uncompressed instructions.
  assign if_instr_pmp_err = pmp_err_if_i |
                            (if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i);

  // Combine bus errors and pmp errors
  assign if_instr_err = if_instr_bus_err | if_instr_pmp_err;

  // Capture the second half of the address for errors on the second part of an instruction
  assign if_instr_err_plus2 = ((if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i) |
                               fetch_err_plus2) & ~pmp_err_if_i;

  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  ibex_compressed_decoder compressed_decoder_i (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .valid_i        (fetch_valid & ~fetch_err),
    .instr_i        (if_instr_rdata),
    .instr_o        (instr_decompressed),
    .is_compressed_o(instr_is_compressed),
    .illegal_instr_o(illegal_c_insn)
  );

  // Dummy instruction insertion
  if (DummyInstructions) begin : gen_dummy_instr
    // SEC_CM: CTRL_FLOW.UNPREDICTABLE
    logic        insert_dummy_instr;
    logic [31:0] dummy_instr_data;

    ibex_dummy_instr #(
      .RndCnstLfsrSeed (RndCnstLfsrSeed),
      .RndCnstLfsrPerm (RndCnstLfsrPerm)
    ) dummy_instr_i (
      .clk_i                (clk_i),
      .rst_ni               (rst_ni),
      .dummy_instr_en_i     (dummy_instr_en_i),
      .dummy_instr_mask_i   (dummy_instr_mask_i),
      .dummy_instr_seed_en_i(dummy_instr_seed_en_i),
      .dummy_instr_seed_i   (dummy_instr_seed_i),
      .fetch_valid_i        (fetch_valid),
      .id_in_ready_i        (id_in_ready_i),
      .insert_dummy_instr_o (insert_dummy_instr),
      .dummy_instr_data_o   (dummy_instr_data)
    );

    // Mux between actual instructions and dummy instructions
    assign instr_out               = insert_dummy_instr ? dummy_instr_data : instr_decompressed;
    assign instr_is_compressed_out = insert_dummy_instr ? 1'b0 : instr_is_compressed;
    assign illegal_c_instr_out     = insert_dummy_instr ? 1'b0 : illegal_c_insn;
    assign instr_err_out           = insert_dummy_instr ? 1'b0 : if_instr_err;

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
    assign instr_out               = instr_decompressed;
    assign instr_is_compressed_out = instr_is_compressed;
    assign illegal_c_instr_out     = illegal_c_insn;
    assign instr_err_out           = if_instr_err;
    assign stall_dummy_instr       = 1'b0;
    assign dummy_instr_id_o        = 1'b0;
  end

  // The ID stage becomes valid as soon as any instruction is registered in the ID stage flops.
  // Note that the current instruction is squashed by the incoming pc_set_i signal.
  // Valid is held until it is explicitly cleared (due to an instruction completing or an exception)
  assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |
                            (instr_valid_id_q & ~instr_valid_clear_i);
  assign instr_new_id_d   = if_instr_valid & id_in_ready_i;

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

  if (ResetAll) begin : g_instr_rdata_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_rdata_id_o         <= '0;
        instr_rdata_alu_id_o     <= '0;
        instr_fetch_err_o        <= '0;
        instr_fetch_err_plus2_o  <= '0;
        instr_rdata_c_id_o       <= '0;
        instr_is_compressed_id_o <= '0;
        illegal_c_insn_id_o      <= '0;
        pc_id_o                  <= '0;
      end else if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= if_instr_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end else begin : g_instr_rdata_nr
    always_ff @(posedge clk_i) begin
      if (if_id_pipe_reg_we) begin
        instr_rdata_id_o         <= instr_out;
        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.
        instr_rdata_alu_id_o     <= instr_out;
        instr_fetch_err_o        <= instr_err_out;
        instr_fetch_err_plus2_o  <= if_instr_err_plus2;
        instr_rdata_c_id_o       <= if_instr_rdata[15:0];
        instr_is_compressed_id_o <= instr_is_compressed_out;
        illegal_c_insn_id_o      <= illegal_c_instr_out;
        pc_id_o                  <= pc_if_o;
      end
    end
  end

  // Check for expected increments of the PC when security hardening enabled
  if (PCIncrCheck) begin : g_secure_pc
    // SEC_CM: PC.CTRL_FLOW.CONSISTENCY
    logic [31:0] prev_instr_addr_incr, prev_instr_addr_incr_buf;
    logic        prev_instr_seq_q, prev_instr_seq_d;

    // Do not check for sequential increase after a branch, jump, exception, interrupt or debug
    // request, all of which will set branch_req. Also do not check after reset or for dummys.
    assign prev_instr_seq_d = (prev_instr_seq_q | instr_new_id_d) &
        ~branch_req & ~if_instr_err & ~stall_dummy_instr;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prev_instr_seq_q <= 1'b0;
      end else begin
        prev_instr_seq_q <= prev_instr_seq_d;
      end
    end

    assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);

    // Buffer anticipated next PC address to ensure optimiser cannot remove the check.
    prim_buf #(.Width(32)) u_prev_instr_addr_incr_buf (
      .in_i (prev_instr_addr_incr),
      .out_o(prev_instr_addr_incr_buf)
    );

    // Check that the address equals the previous address +2/+4
    assign pc_mismatch_alert_o = prev_instr_seq_q & (pc_if_o != prev_instr_addr_incr_buf);

  end else begin : g_no_secure_pc
    assign pc_mismatch_alert_o = 1'b0;
  end

  if (BranchPredictor) begin : g_branch_predictor
    logic [31:0] instr_skid_data_q;
    logic [31:0] instr_skid_addr_q;
    logic        instr_skid_bp_taken_q;
    logic        instr_skid_valid_q, instr_skid_valid_d;
    logic        instr_skid_en;
    logic        instr_bp_taken_q, instr_bp_taken_d;

    logic        predict_branch_taken_raw;

    // ID stages needs to know if branch was predicted taken so it can signal mispredicts
    if (ResetAll) begin : g_bp_taken_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          instr_bp_taken_q <= '0;
        end else if (if_id_pipe_reg_we) begin
          instr_bp_taken_q <= instr_bp_taken_d;
        end
      end
    end else begin : g_bp_taken_nr
      always_ff @(posedge clk_i) begin
        if (if_id_pipe_reg_we) begin
          instr_bp_taken_q <= instr_bp_taken_d;
        end
      end
    end

    // When branch prediction is enabled a skid buffer between the IF and ID/EX stage is introduced.
    // If an instruction in IF is predicted to be a taken branch and ID/EX is not ready the
    // instruction in IF is moved to the skid buffer which becomes the output of the IF stage until
    // the ID/EX stage accepts the instruction. The skid buffer is required as otherwise the ID/EX
    // ready signal is coupled to the instr_req_o output which produces a feedthrough path from
    // data_gnt_i -> instr_req_o (which needs to be avoided as for some interconnects this will
    // result in a combinational loop).

    assign instr_skid_en = predict_branch_taken & ~pc_set_i & ~id_in_ready_i & ~instr_skid_valid_q;

    assign instr_skid_valid_d = (instr_skid_valid_q & ~id_in_ready_i & ~stall_dummy_instr) |
                                instr_skid_en;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        instr_skid_valid_q <= 1'b0;
      end else begin
        instr_skid_valid_q <= instr_skid_valid_d;
      end
    end

    if (ResetAll) begin : g_instr_skid_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          instr_skid_bp_taken_q <= '0;
          instr_skid_data_q     <= '0;
          instr_skid_addr_q     <= '0;
        end else if (instr_skid_en) begin
          instr_skid_bp_taken_q <= predict_branch_taken;
          instr_skid_data_q     <= fetch_rdata;
          instr_skid_addr_q     <= fetch_addr;
        end
      end
    end else begin : g_instr_skid_nr
      always_ff @(posedge clk_i) begin
        if (instr_skid_en) begin
          instr_skid_bp_taken_q <= predict_branch_taken;
          instr_skid_data_q     <= fetch_rdata;
          instr_skid_addr_q     <= fetch_addr;
        end
      end
    end

    ibex_branch_predict branch_predict_i (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .fetch_rdata_i(fetch_rdata),
      .fetch_pc_i   (fetch_addr),
      .fetch_valid_i(fetch_valid),

      .predict_branch_taken_o(predict_branch_taken_raw),
      .predict_branch_pc_o   (predict_branch_pc)
    );

    // If there is an instruction in the skid buffer there must be no branch prediction.
    // Instructions are only placed in the skid after they have been predicted to be a taken branch
    // so with the skid valid any prediction has already occurred.
    // Do not branch predict on instruction errors.
    assign predict_branch_taken = predict_branch_taken_raw & ~instr_skid_valid_q & ~fetch_err;

    assign if_instr_valid   = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);
    assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;
    assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;

    // Don't branch predict on instruction error so only instructions without errors end up in the
    // skid buffer.
    assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;
    assign instr_bp_taken_d = instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken;

    assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;

    assign instr_bp_taken_o = instr_bp_taken_q;

    `ASSERT(NoPredictSkid, instr_skid_valid_q |-> ~predict_branch_taken)
    `ASSERT(NoPredictIllegal, predict_branch_taken |-> ~illegal_c_insn)
  end else begin : g_no_branch_predictor
    assign instr_bp_taken_o     = 1'b0;
    assign predict_branch_taken = 1'b0;
    assign predict_branch_pc    = 32'b0;

    assign if_instr_valid = fetch_valid;
    assign if_instr_rdata = fetch_rdata;
    assign if_instr_addr  = fetch_addr;
    assign if_instr_bus_err = fetch_err;
    assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN(IbexExcPcMuxKnown, exc_pc_mux_i)

  if (BranchPredictor) begin : g_branch_predictor_asserts
    `ASSERT_IF(IbexPcMuxValid, pc_mux_internal inside {
        PC_BOOT,
        PC_JUMP,
        PC_EXC,
        PC_ERET,
        PC_DRET,
        PC_BP},
      pc_set_i)

`ifdef INC_ASSERT
    /**
     * Checks for branch prediction interface to fetch_fifo/icache
     *
     * The interface has two signals:
     * - predicted_branch_i: When set with a branch (branch_i) indicates the branch is a predicted
     *   one, it should be ignored when a branch_i isn't set.
     * - branch_mispredict_i: Indicates the previously predicted branch was mis-predicted and
     *   execution should resume with the not-taken side of the branch (i.e. continue with the PC
     *   that followed the predicted branch). This must be raised before the instruction that is
     *   made available following a predicted branch is accepted (Following a cycle with branch_i
     *   & predicted_branch_i, branch_mispredict_i can only be asserted before or on the same cycle
     *   as seeing fetch_valid & fetch_ready). When branch_mispredict_i is asserted, fetch_valid may
     *   be asserted in response. If fetch_valid is asserted on the same cycle as
     *   branch_mispredict_i this indicates the fetch_fifo/icache has the not-taken side of the
     *   branch immediately ready for use
     */
    logic        predicted_branch_live_q, predicted_branch_live_d;
    logic [31:0] predicted_branch_nt_pc_q, predicted_branch_nt_pc_d;
    logic [31:0] awaiting_instr_after_mispredict_q, awaiting_instr_after_mispredict_d;
    logic [31:0] next_pc;

    logic mispredicted, mispredicted_d, mispredicted_q;

    assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);

    logic predicted_branch;

    // pc_set_i takes precendence over branch prediction
    assign predicted_branch = predict_branch_taken & ~pc_set_i;

    always_comb begin
      predicted_branch_live_d = predicted_branch_live_q;
      mispredicted_d          = mispredicted_q;

      if (branch_req & predicted_branch) begin
        predicted_branch_live_d = 1'b1;
        mispredicted_d          = 1'b0;
      end else if (predicted_branch_live_q) begin
        if (fetch_valid & fetch_ready) begin
          predicted_branch_live_d = 1'b0;
        end else if (nt_branch_mispredict_i) begin
          mispredicted_d = 1'b1;
        end
      end
    end

    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        predicted_branch_live_q <= 1'b0;
        mispredicted_q          <= 1'b0;
      end else begin
        predicted_branch_live_q <= predicted_branch_live_d;
        mispredicted_q          <= mispredicted_d;
      end
    end

    always @(posedge clk_i) begin
      if (branch_req & predicted_branch) begin
        predicted_branch_nt_pc_q <= next_pc;
      end
    end

    // Must only see mispredict after we've performed a predicted branch but before we've accepted
    // any instruction (with fetch_ready & fetch_valid) that follows that predicted branch.
    `ASSERT(MispredictOnlyImmediatelyAfterPredictedBranch,
      nt_branch_mispredict_i |-> predicted_branch_live_q)
    // Check that on mispredict we get the correct PC for the non-taken side of the branch when
    // prefetch buffer/icache makes that PC available.
    `ASSERT(CorrectPCOnMispredict,
      predicted_branch_live_q & mispredicted_d & fetch_valid |->
      fetch_addr == predicted_branch_nt_pc_q)
    // Must not signal mispredict over multiple cycles but it's possible to have back to back
    // mispredicts for different branches (core signals mispredict, prefetch buffer/icache immediate
    // has not-taken side of the mispredicted branch ready, which itself is a predicted branch,
    // following cycle core signal that that branch has mispredicted).
    `ASSERT(MispredictSingleCycle,
      nt_branch_mispredict_i & ~(fetch_valid & fetch_ready) |=> ~nt_branch_mispredict_i)
`endif

  end else begin : g_no_branch_predictor_asserts
    `ASSERT_IF(IbexPcMuxValid, pc_mux_internal inside {
        PC_BOOT,
        PC_JUMP,
        PC_EXC,
        PC_ERET,
        PC_DRET},
      pc_set_i)
  end

  // Boot address must be aligned to 256 bytes.
  `ASSERT(IbexBootAddrUnaligned, boot_addr_i[7:0] == 8'h00)

  // Address must not contain X when request is sent.
  `ASSERT(IbexInstrAddrUnknown, instr_req_o |-> !$isunknown(instr_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexInstrAddrUnaligned, instr_req_o |-> (instr_addr_o[1:0] == 2'b00))

endmodule
