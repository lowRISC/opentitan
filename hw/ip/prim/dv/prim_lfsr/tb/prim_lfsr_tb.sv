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
  localparam string           LfsrType   = `LFSR_TYPE;
`else
  localparam string           LfsrType   = "GAL_XOR";
`endif
`ifdef MIN_LFSR_DW
  localparam int unsigned     MinLfsrDw  = `MIN_LFSR_DW;
`else
  localparam int unsigned     MinLfsrDw  = 4;
`endif
`ifdef MAX_LFSR_DW
  localparam int unsigned     MaxLfsrDw  = `MAX_LFSR_DW;
`else
  localparam int unsigned     MaxLfsrDw  = 32;
`endif

  // leave this constant
  localparam logic SEED       = 1'b1;

  localparam time  ClkPeriod  = 10000;

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

  // This is used to specify an identity permutation via the custom state output
  // permutation parameter for all LFSRs up to 256bit wide.
  localparam logic [255:0][31:0] StatePerm = '{
    32'd255, 32'd254, 32'd253, 32'd252, 32'd251, 32'd250, 32'd249, 32'd248,
    32'd247, 32'd246, 32'd245, 32'd244, 32'd243, 32'd242, 32'd241, 32'd240,
    32'd239, 32'd238, 32'd237, 32'd236, 32'd235, 32'd234, 32'd233, 32'd232,
    32'd231, 32'd230, 32'd229, 32'd228, 32'd227, 32'd226, 32'd225, 32'd224,
    32'd223, 32'd222, 32'd221, 32'd220, 32'd219, 32'd218, 32'd217, 32'd216,
    32'd215, 32'd214, 32'd213, 32'd212, 32'd211, 32'd210, 32'd209, 32'd208,
    32'd207, 32'd206, 32'd205, 32'd204, 32'd203, 32'd202, 32'd201, 32'd200,
    32'd199, 32'd198, 32'd197, 32'd196, 32'd195, 32'd194, 32'd193, 32'd192,
    32'd191, 32'd190, 32'd189, 32'd188, 32'd187, 32'd186, 32'd185, 32'd184,
    32'd183, 32'd182, 32'd181, 32'd180, 32'd179, 32'd178, 32'd177, 32'd176,
    32'd175, 32'd174, 32'd173, 32'd172, 32'd171, 32'd170, 32'd169, 32'd168,
    32'd167, 32'd166, 32'd165, 32'd164, 32'd163, 32'd162, 32'd161, 32'd160,
    32'd159, 32'd158, 32'd157, 32'd156, 32'd155, 32'd154, 32'd153, 32'd152,
    32'd151, 32'd150, 32'd149, 32'd148, 32'd147, 32'd146, 32'd145, 32'd144,
    32'd143, 32'd142, 32'd141, 32'd140, 32'd139, 32'd138, 32'd137, 32'd136,
    32'd135, 32'd134, 32'd133, 32'd132, 32'd131, 32'd130, 32'd129, 32'd128,
    32'd127, 32'd126, 32'd125, 32'd124, 32'd123, 32'd122, 32'd121, 32'd120,
    32'd119, 32'd118, 32'd117, 32'd116, 32'd115, 32'd114, 32'd113, 32'd112,
    32'd111, 32'd110, 32'd109, 32'd108, 32'd107, 32'd106, 32'd105, 32'd104,
    32'd103, 32'd102, 32'd101, 32'd100, 32'd099, 32'd098, 32'd097, 32'd096,
    32'd095, 32'd094, 32'd093, 32'd092, 32'd091, 32'd090, 32'd089, 32'd088,
    32'd087, 32'd086, 32'd085, 32'd084, 32'd083, 32'd082, 32'd081, 32'd080,
    32'd079, 32'd078, 32'd077, 32'd076, 32'd075, 32'd074, 32'd073, 32'd072,
    32'd071, 32'd070, 32'd069, 32'd068, 32'd067, 32'd066, 32'd065, 32'd064,
    32'd063, 32'd062, 32'd061, 32'd060, 32'd059, 32'd058, 32'd057, 32'd056,
    32'd055, 32'd054, 32'd053, 32'd052, 32'd051, 32'd050, 32'd049, 32'd048,
    32'd047, 32'd046, 32'd045, 32'd044, 32'd043, 32'd042, 32'd041, 32'd040,
    32'd039, 32'd038, 32'd037, 32'd036, 32'd035, 32'd034, 32'd033, 32'd032,
    32'd031, 32'd030, 32'd029, 32'd028, 32'd027, 32'd026, 32'd025, 32'd024,
    32'd023, 32'd022, 32'd021, 32'd020, 32'd019, 32'd018, 32'd017, 32'd016,
    32'd015, 32'd014, 32'd013, 32'd012, 32'd011, 32'd010, 32'd009, 32'd008,
    32'd007, 32'd006, 32'd005, 32'd004, 32'd003, 32'd002, 32'd001, 32'd000
  };

  `ASSERT_INIT(MaxStateSizeCheck_A, MaxLfsrDw < 256)

  logic [MaxLfsrDw:0] lfsr_en, err;
  logic [MaxLfsrDw:MinLfsrDw][MaxLfsrDw-1:0] state_out;
  logic [MaxLfsrDw:MinLfsrDw][MaxLfsrDw-1:0] lfsr_periods;

  for (genvar k = MinLfsrDw; k <= MaxLfsrDw; k++) begin : gen_duts
    prim_lfsr #(
      .LfsrType    ( LfsrType ),
      .LfsrDw      ( k        ),
      .EntropyDw   ( 1        ),
      .StateOutDw  ( k        ),
      .DefaultSeed ( k'(SEED) ),
      // The case where this is disabled is already tested with FPV.
      // Hence we cover the enabled case with custom permutations
      // in this testbench.
      .StatePermEn ( 1'b1     ),
      .StatePerm   ( StatePerm[MaxLfsrDw-1:0] ),
      // Enable internal max length check.
      .MaxLenSVA   ( 1'b1     )
    ) i_prim_lfsr (
      .clk_i         ( clk                 ),
      .rst_ni        ( rst_n               ),
      .seed_en_i     ( 1'b0                ),
      .seed_i        ( '0                  ),
      .lfsr_en_i     ( lfsr_en[k]          ),
      .entropy_i     ( 1'b0                ),
      .state_o       ( state_out[k][k-1:0] )
    );

    if (k < MaxLfsrDw) begin : gen_tie_off
      assign state_out[k][MaxLfsrDw-1:k] = '0;
    end

    // calculate period of LFSR:
    assign lfsr_periods[k] = MaxLfsrDw'({{(k-1){1'b1}}, 1'b0});
  end

//////////////////////////////////////////////////////
// stimuli application / response checking
//////////////////////////////////////////////////////

  initial begin : p_stimuli
    lfsr_en = '0;
    err     = '0;

    main_clk.set_period_ns(ClkPeriod);
    main_clk.set_active();
    main_clk.apply_reset();

    $display("LFSR maxlen test started for %s (%0d bit to %0d bit).",
        LfsrType, MinLfsrDw, MaxLfsrDw);

    main_clk.wait_clks(10);

    // enable all LFSRs
    lfsr_en = '1;

    $display("Running for 2**%0d-1 cycles...", MaxLfsrDw);
    for (longint unsigned k = 0; k <= lfsr_periods[MaxLfsrDw]; k++ ) begin

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
      $display("All LFSRs from %0d bit to %0d have maximum length!",
          MinLfsrDw, MaxLfsrDw);
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
