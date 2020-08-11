// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_lfsr, sweeps through all implementations
// within a certain range to check whether they are max length.

module prim_lfsr_tb;

  //////////////////////////////////////////////////////
  // config
  //////////////////////////////////////////////////////

  // this can be overriden on the command line
  // supported types are GAL_XOR, FIB_XNOR
`ifdef LFSR_TYPE
  localparam string LfsrType = `LFSR_TYPE;
`else
  localparam string LfsrType = "GAL_XOR";
`endif
`ifdef MIN_LFSR_DW
  localparam int unsigned MinLfsrDw = `MIN_LFSR_DW;
`else
  localparam int unsigned MinLfsrDw = 4;
`endif
`ifdef MAX_LFSR_DW
  localparam int unsigned MaxLfsrDw = `MAX_LFSR_DW;
`else
  localparam int unsigned MaxLfsrDw = 32;
`endif

  // leave this constant
  localparam logic SEED = 1'b1;

  localparam time ClkPeriod = 10000;

  //////////////////////////////////////////////////////
  // clock
  //////////////////////////////////////////////////////

  wire clk, rst_n;

  clk_rst_if main_clk (
      .clk,
      .rst_n
  );

  //////////////////////////////////////////////////////
  // DUTs
  //////////////////////////////////////////////////////

  logic [MaxLfsrDw:0] lfsr_en, err;
  logic [MaxLfsrDw:MinLfsrDw][MaxLfsrDw-1:0] state_out;
  logic [MaxLfsrDw:MinLfsrDw][MaxLfsrDw-1:0] lfsr_periods;

  for (genvar k = MinLfsrDw; k <= MaxLfsrDw; k++) begin : gen_duts
    prim_lfsr #(
        .LfsrType(LfsrType),
        .LfsrDw(k),
        .EntropyDw(1),
        .StateOutDw(k),
        .DefaultSeed(k'(SEED)),
        // enable internal max length check
        .MaxLenSVA(1'b1)
    ) i_prim_lfsr (
        .clk_i    (clk),
        .rst_ni   (rst_n),
        .seed_en_i(1'b0),
        .seed_i   ('0),
        .lfsr_en_i(lfsr_en[k]),
        .entropy_i(1'b0),
        .state_o  (state_out[k][k - 1:0])
    );

    if (k < MaxLfsrDw) begin : gen_tie_off
      assign state_out[k][MaxLfsrDw - 1:k] = '0;
    end

    // calculate period of LFSR:
    assign lfsr_periods[k] = MaxLfsrDw'({{(k - 1) {1'b1}}, 1'b0});
  end

  //////////////////////////////////////////////////////
  // stimuli application / response checking
  //////////////////////////////////////////////////////

  initial begin : p_stimuli
    lfsr_en = '0;
    err = '0;

    main_clk.set_period_ns(ClkPeriod);
    main_clk.set_active();
    main_clk.apply_reset();

    $display("LFSR maxlen test started for %s (%0d bit to %0d bit).", LfsrType, MinLfsrDw,
             MaxLfsrDw);

    main_clk.wait_clks(10);

    // enable all LFSRs
    lfsr_en = '1;

    $display("Running for 2**%0d-1 cycles...", MaxLfsrDw);
    for (longint unsigned k = 0; k <= lfsr_periods[MaxLfsrDw]; k++) begin

      main_clk.wait_clks(1);

      for (int unsigned j = MinLfsrDw; j <= MaxLfsrDw; j++) begin
        // check if we reached the initial state again
        if (state_out[j] == MaxLfsrDw'(SEED) && lfsr_en[j]) begin
          // $display("cycle: %d -- lfsr: %d -- %x ?= %x, %x",
          // k, j, state_out[j], SEED, lfsr_en);
          lfsr_en[j] = 1'b0;
          // we expect this to occur only after the maximum length period
          if (lfsr_periods[j] == k) begin
            $display("Maxlen check for LFSR %0d succeeded!", j);
          end else begin
            err[j] = 1'b1;
            $error("Error LFSR %0d is not maximal length!", j);
          end
        end
      end
    end

    main_clk.wait_clks(10);

    for (int unsigned j = MinLfsrDw; j <= MaxLfsrDw; j++) begin
      if (lfsr_en[j]) begin
        $error("Error LFSR %0d never got back to initial state!", j);
        err[j] = 1'b1;
      end
    end

    if (!err) begin
      $display("All LFSRs from %0d bit to %0d have maximum length!", MinLfsrDw, MaxLfsrDw);
      // signature for makefile
      $display("TEST PASSED CHECKS");
    end else begin
      $display("One or more checks have failed!");
      // signature for makefile
      $display("TEST FAILED CHECKS");
    end

    $finish();
  end


endmodule : prim_lfsr_tb
