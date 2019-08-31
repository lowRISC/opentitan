// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31 or 15x 32 bit wide registers.        //
//                 Register 0 is fixed to 0. This register file is based on   //
//                 latches and is thus smaller than the flip-flop based RF.   //
//                 It requires a target technology-specific clock gating      //
//                 cell. Use this register file when targeting ASIC           //
//                 synthesis or event-based simulators.                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on latches and is thus smaller than the flip-flop
 * based RF. It requires a target technology-specific clock gating cell. Use this
 * register file when targeting ASIC synthesis or event-based simulators.
 */
module ibex_register_file #(
    parameter bit RV32E              = 0,
    parameter int unsigned DataWidth = 32
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    input  logic                 test_en_i,

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

  // Write port W1
  logic [ADDR_WIDTH-1:0] raddr_a_int, raddr_b_int, waddr_a_int;

  assign raddr_a_int = raddr_a_i[ADDR_WIDTH-1:0];
  assign raddr_b_int = raddr_b_i[ADDR_WIDTH-1:0];
  assign waddr_a_int = waddr_a_i[ADDR_WIDTH-1:0];

  logic clk_int;

  //////////////////////////////////////
  // READ: Read address decoder (RAD) //
  //////////////////////////////////////
  assign rdata_a_o = mem[raddr_a_int];
  assign rdata_b_o = mem[raddr_b_int];

  ///////////////////////////////
  // WRITE: SAMPLE INPUT DATA //
  ///////////////////////////////

  prim_clock_gating cg_we_global (
      .clk_i     ( clk_i           ),
      .en_i      ( we_a_i          ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk_int         )
  );

  // use clk_int here, since otherwise we don't want to write anything anyway
  always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
    if (!rst_ni) begin
      wdata_a_q   <= '0;
    end else begin
      if (we_a_i) begin
        wdata_a_q <= wdata_a_i;
      end
    end
  end

  ///////////////////////////////////////////////////////////////
  // WRITE: Write Address Decoder (WAD), combinatorial process //
  ///////////////////////////////////////////////////////////////
  always_comb begin : wad
    for (int i = 1; i < NUM_WORDS; i++) begin : wad_word_iter
      if (we_a_i && (waddr_a_int == i)) begin
        waddr_onehot_a[i] = 1'b1;
      end else begin
        waddr_onehot_a[i] = 1'b0;
      end
    end
  end

  //////////////////////////////////////////////////////////////////////////
  // WRITE: Clock gating (if integrated clock-gating cells are available) //
  //////////////////////////////////////////////////////////////////////////
  for (genvar x = 1; x < NUM_WORDS; x++) begin : gen_cg_word_iter
    prim_clock_gating cg_i (
        .clk_i     ( clk_int           ),
        .en_i      ( waddr_onehot_a[x] ),
        .test_en_i ( test_en_i         ),
        .clk_o     ( mem_clocks[x]     )
    );
  end

  ////////////////////////////
  // WRITE: Write operation //
  ////////////////////////////
  // Generate M = WORDS sequential processes, each of which describes one
  // word of the memory. The processes are synchronized with the clocks
  // ClocksxC(i), i = 0, 1, ..., M-1
  // Use active low, i.e. transparent on low latches as storage elements
  // Data is sampled on rising clock edge

  always_latch begin : latch_wdata
    // Note: The assignment has to be done inside this process or Modelsim complains about it
    mem[0] = '0;

    for (int k = 1; k < NUM_WORDS; k++) begin : latch_wdata_word_iter
      if (mem_clocks[k]) begin
        mem[k] = wdata_a_q;
      end
    end
  end

`ifdef VERILATOR
  initial begin
    $display("Latch-based register file not supported for Verilator simulation");
    $fatal;
  end
`endif

endmodule
