// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on latches and is thus smaller than the flip-flop
 * based RF. It requires a target technology-specific clock gating cell. Use this
 * register file when targeting ASIC synthesis or event-based simulators.
 */
module ibex_register_file_latch #(
    parameter bit          RV32E             = 0,
    parameter int unsigned DataWidth         = 32,
    parameter bit          DummyInstructions = 0
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    input  logic                 test_en_i,
    input  logic                 dummy_instr_id_i,

    //Read port R1
    input  logic [4:0]           raddr_a_i,
    output logic [DataWidth-1:0] rdata_a_o,

    //Read port R2
    input  logic [4:0]           raddr_b_i,
    output logic [DataWidth-1:0] rdata_b_o,

    // Write port W1
    input  logic [4:0]           waddr_a_i,
    input  logic [DataWidth-1:0] wdata_a_i,
    input  logic                 we_a_i

);

  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [DataWidth-1:0] mem[NUM_WORDS];

  logic [NUM_WORDS-1:1] waddr_onehot_a;

  logic [NUM_WORDS-1:1] mem_clocks;
  logic [DataWidth-1:0] wdata_a_q;

  // internal addresses
  logic [ADDR_WIDTH-1:0] raddr_a_int, raddr_b_int, waddr_a_int;

  assign raddr_a_int = raddr_a_i[ADDR_WIDTH-1:0];
  assign raddr_b_int = raddr_b_i[ADDR_WIDTH-1:0];
  assign waddr_a_int = waddr_a_i[ADDR_WIDTH-1:0];

  logic clk_int;

  //////////
  // READ //
  //////////
  assign rdata_a_o = mem[raddr_a_int];
  assign rdata_b_o = mem[raddr_b_int];

  ///////////
  // WRITE //
  ///////////
  // Global clock gating
  prim_clock_gating cg_we_global (
      .clk_i     ( clk_i     ),
      .en_i      ( we_a_i    ),
      .test_en_i ( test_en_i ),
      .clk_o     ( clk_int   )
  );

  // Sample input data
  // Use clk_int here, since otherwise we don't want to write anything anyway.
  always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
    if (!rst_ni) begin
      wdata_a_q   <= '0;
    end else begin
      if (we_a_i) begin
        wdata_a_q <= wdata_a_i;
      end
    end
  end

  // Write address decoding
  always_comb begin : wad
    for (int i = 1; i < NUM_WORDS; i++) begin : wad_word_iter
      if (we_a_i && (waddr_a_int == 5'(i))) begin
        waddr_onehot_a[i] = 1'b1;
      end else begin
        waddr_onehot_a[i] = 1'b0;
      end
    end
  end

  // Individual clock gating (if integrated clock-gating cells are available)
  for (genvar x = 1; x < NUM_WORDS; x++) begin : gen_cg_word_iter
    prim_clock_gating cg_i (
        .clk_i     ( clk_int           ),
        .en_i      ( waddr_onehot_a[x] ),
        .test_en_i ( test_en_i         ),
        .clk_o     ( mem_clocks[x]     )
    );
  end

  // Actual write operation:
  // Generate the sequential process for the NUM_WORDS words of the memory.
  // The process is synchronized with the clocks mem_clocks[i], i = 1, ..., NUM_WORDS-1.
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_latches
    always_latch begin
      if (mem_clocks[i]) begin
        mem[i] = wdata_a_q;
      end
    end
  end

  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    logic                 we_r0_dummy;
    logic                 r0_clock;
    logic [DataWidth-1:0] mem_r0;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_id_i;

    // R0 clock gate
    prim_clock_gating cg_i (
        .clk_i     ( clk_int     ),
        .en_i      ( we_r0_dummy ),
        .test_en_i ( test_en_i   ),
        .clk_o     ( r0_clock    )
    );

    always_latch begin : latch_wdata
      if (r0_clock) begin
        mem_r0 = wdata_a_q;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign mem[0] = dummy_instr_id_i ? mem_r0 : '0;

  end else begin : g_normal_r0
    logic unused_dummy_instr_id;
    assign unused_dummy_instr_id = dummy_instr_id_i;

    assign mem[0] = '0;
  end

`ifdef VERILATOR
  initial begin
    $display("Latch-based register file not supported for Verilator simulation");
    $fatal;
  end
`endif

endmodule
