// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_lfsr, sweeps through all implementations
// within a certain range to check whether they are max length.

module prim_lfsr_tb;

  import dv_utils_pkg::*;
  `include "dv_macros.svh"

  //////////////////////////////////////////////////////
  // Build configurations:
  // LFSR_FIB_TYPE; If defined, "FIB_XNOR" is used.
  //                If not defined, this defaults to "GAL_XOR".
  // MIN_LFSR_DW: Minimum LFSR width tested.
  // MAX_LFSR_DW: Maximum LFSR width tested.
  //////////////////////////////////////////////////////
`ifdef LFSR_FIB_TYPE
  localparam string           LfsrType   = "FIB_XNOR";
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

  // The default seed of the LFSR.
  //
  // This is fixed to 1. It is unused in simulations. The `prim_lfsr` instead, randomizes the
  // default seed value (DefaultSeedLocal) at runtime. This is enforced with
  // +prim_lfsr_use_default_seed=0 plusarg.
  localparam logic SEED = 1'b1;

  // The StatePerm below is only defined for LFSRs up to 256bit wide.
  `ASSERT_INIT(MaxStateSizeCheck_A, MaxLfsrDw < 256)

  logic [MaxLfsrDw:MinLfsrDw] err, test_done;
  logic                 lfsr_en      [MaxLfsrDw+1];
  logic                 seed_en      [MaxLfsrDw+1];
  logic [MaxLfsrDw-1:0] state_out    [MaxLfsrDw+1];
  logic [MaxLfsrDw-1:0] lfsr_periods [MaxLfsrDw+1];
  logic [MaxLfsrDw-1:0] entropy      [MaxLfsrDw+1];
  logic [MaxLfsrDw-1:0] seed         [MaxLfsrDw+1];
  logic [MaxLfsrDw-1:0] rand_entropy;
  logic [MaxLfsrDw-1:0] rand_seed;


  for (genvar k = MinLfsrDw; k <= MaxLfsrDw; k++) begin : gen_duts
    // This is used to specify an identity permutation via the custom state output
    // permutation parameter for all LFSRs up to 256bit wide.
    localparam int Dw = $clog2(k);
    localparam logic [255:0][Dw-1:0] StatePerm = '{
      Dw'(32'd255), Dw'(32'd254), Dw'(32'd253), Dw'(32'd252),
      Dw'(32'd251), Dw'(32'd250), Dw'(32'd249), Dw'(32'd248),
      Dw'(32'd247), Dw'(32'd246), Dw'(32'd245), Dw'(32'd244),
      Dw'(32'd243), Dw'(32'd242), Dw'(32'd241), Dw'(32'd240),
      Dw'(32'd239), Dw'(32'd238), Dw'(32'd237), Dw'(32'd236),
      Dw'(32'd235), Dw'(32'd234), Dw'(32'd233), Dw'(32'd232),
      Dw'(32'd231), Dw'(32'd230), Dw'(32'd229), Dw'(32'd228),
      Dw'(32'd227), Dw'(32'd226), Dw'(32'd225), Dw'(32'd224),
      Dw'(32'd223), Dw'(32'd222), Dw'(32'd221), Dw'(32'd220),
      Dw'(32'd219), Dw'(32'd218), Dw'(32'd217), Dw'(32'd216),
      Dw'(32'd215), Dw'(32'd214), Dw'(32'd213), Dw'(32'd212),
      Dw'(32'd211), Dw'(32'd210), Dw'(32'd209), Dw'(32'd208),
      Dw'(32'd207), Dw'(32'd206), Dw'(32'd205), Dw'(32'd204),
      Dw'(32'd203), Dw'(32'd202), Dw'(32'd201), Dw'(32'd200),
      Dw'(32'd199), Dw'(32'd198), Dw'(32'd197), Dw'(32'd196),
      Dw'(32'd195), Dw'(32'd194), Dw'(32'd193), Dw'(32'd192),
      Dw'(32'd191), Dw'(32'd190), Dw'(32'd189), Dw'(32'd188),
      Dw'(32'd187), Dw'(32'd186), Dw'(32'd185), Dw'(32'd184),
      Dw'(32'd183), Dw'(32'd182), Dw'(32'd181), Dw'(32'd180),
      Dw'(32'd179), Dw'(32'd178), Dw'(32'd177), Dw'(32'd176),
      Dw'(32'd175), Dw'(32'd174), Dw'(32'd173), Dw'(32'd172),
      Dw'(32'd171), Dw'(32'd170), Dw'(32'd169), Dw'(32'd168),
      Dw'(32'd167), Dw'(32'd166), Dw'(32'd165), Dw'(32'd164),
      Dw'(32'd163), Dw'(32'd162), Dw'(32'd161), Dw'(32'd160),
      Dw'(32'd159), Dw'(32'd158), Dw'(32'd157), Dw'(32'd156),
      Dw'(32'd155), Dw'(32'd154), Dw'(32'd153), Dw'(32'd152),
      Dw'(32'd151), Dw'(32'd150), Dw'(32'd149), Dw'(32'd148),
      Dw'(32'd147), Dw'(32'd146), Dw'(32'd145), Dw'(32'd144),
      Dw'(32'd143), Dw'(32'd142), Dw'(32'd141), Dw'(32'd140),
      Dw'(32'd139), Dw'(32'd138), Dw'(32'd137), Dw'(32'd136),
      Dw'(32'd135), Dw'(32'd134), Dw'(32'd133), Dw'(32'd132),
      Dw'(32'd131), Dw'(32'd130), Dw'(32'd129), Dw'(32'd128),
      Dw'(32'd127), Dw'(32'd126), Dw'(32'd125), Dw'(32'd124),
      Dw'(32'd123), Dw'(32'd122), Dw'(32'd121), Dw'(32'd120),
      Dw'(32'd119), Dw'(32'd118), Dw'(32'd117), Dw'(32'd116),
      Dw'(32'd115), Dw'(32'd114), Dw'(32'd113), Dw'(32'd112),
      Dw'(32'd111), Dw'(32'd110), Dw'(32'd109), Dw'(32'd108),
      Dw'(32'd107), Dw'(32'd106), Dw'(32'd105), Dw'(32'd104),
      Dw'(32'd103), Dw'(32'd102), Dw'(32'd101), Dw'(32'd100),
      Dw'(32'd099), Dw'(32'd098), Dw'(32'd097), Dw'(32'd096),
      Dw'(32'd095), Dw'(32'd094), Dw'(32'd093), Dw'(32'd092),
      Dw'(32'd091), Dw'(32'd090), Dw'(32'd089), Dw'(32'd088),
      Dw'(32'd087), Dw'(32'd086), Dw'(32'd085), Dw'(32'd084),
      Dw'(32'd083), Dw'(32'd082), Dw'(32'd081), Dw'(32'd080),
      Dw'(32'd079), Dw'(32'd078), Dw'(32'd077), Dw'(32'd076),
      Dw'(32'd075), Dw'(32'd074), Dw'(32'd073), Dw'(32'd072),
      Dw'(32'd071), Dw'(32'd070), Dw'(32'd069), Dw'(32'd068),
      Dw'(32'd067), Dw'(32'd066), Dw'(32'd065), Dw'(32'd064),
      Dw'(32'd063), Dw'(32'd062), Dw'(32'd061), Dw'(32'd060),
      Dw'(32'd059), Dw'(32'd058), Dw'(32'd057), Dw'(32'd056),
      Dw'(32'd055), Dw'(32'd054), Dw'(32'd053), Dw'(32'd052),
      Dw'(32'd051), Dw'(32'd050), Dw'(32'd049), Dw'(32'd048),
      Dw'(32'd047), Dw'(32'd046), Dw'(32'd045), Dw'(32'd044),
      Dw'(32'd043), Dw'(32'd042), Dw'(32'd041), Dw'(32'd040),
      Dw'(32'd039), Dw'(32'd038), Dw'(32'd037), Dw'(32'd036),
      Dw'(32'd035), Dw'(32'd034), Dw'(32'd033), Dw'(32'd032),
      Dw'(32'd031), Dw'(32'd030), Dw'(32'd029), Dw'(32'd028),
      Dw'(32'd027), Dw'(32'd026), Dw'(32'd025), Dw'(32'd024),
      Dw'(32'd023), Dw'(32'd022), Dw'(32'd021), Dw'(32'd020),
      Dw'(32'd019), Dw'(32'd018), Dw'(32'd017), Dw'(32'd016),
      Dw'(32'd015), Dw'(32'd014), Dw'(32'd013), Dw'(32'd012),
      Dw'(32'd011), Dw'(32'd010), Dw'(32'd009), Dw'(32'd008),
      Dw'(32'd007), Dw'(32'd006), Dw'(32'd005), Dw'(32'd004),
      Dw'(32'd003), Dw'(32'd002), Dw'(32'd001), Dw'(32'd000)
    };

    //////////////////////////////////////////////////////
    // clock & reset
    //////////////////////////////////////////////////////
    wire clk, rst_n;
    clk_rst_if main_clk(.clk, .rst_n);

   //////////////////////////////////////////////////////
   // DUTs
   //////////////////////////////////////////////////////
   prim_lfsr #(
      .LfsrType    ( LfsrType ),
      .LfsrDw      ( k        ),
      .EntropyDw   ( k        ),
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
      .seed_en_i     ( seed_en[k]          ),
      .seed_i        ( seed[k][k-1:0]      ),
      .lfsr_en_i     ( lfsr_en[k]          ),
      .entropy_i     ( entropy[k][k-1:0]   ),
      .state_o       ( state_out[k][k-1:0] )
    );

    if (k < MaxLfsrDw) begin : gen_tie_off
      assign state_out[k][MaxLfsrDw-1:k] = '0;
    end

    // calculate period of LFSR:
    assign lfsr_periods[k] = MaxLfsrDw'({{(k-1){1'b1}}, 1'b0});

    //////////////////////////////////////////////////////
    // stimuli application / response checking
    //////////////////////////////////////////////////////
    initial begin : p_stimuli
      bit [k-1:0] actual_default_seed;

      lfsr_en[k] = 0;
      seed_en[k] = 0;
      seed[k] = 0;
      entropy[k] = 0;
      err[k] = 0;
      test_done[k] = 0;

      main_clk.set_sole_clock(1);
      main_clk.set_active();
      main_clk.apply_reset();
      main_clk.wait_clks($urandom_range(2, 20));

      ////////////////////////////////
      // Smoke Check
      ////////////////////////////////

      // For simulations, we modify prim_lfsr to pick a random default seed for every
      // invocation, instead of going with the DefaultSeed parameter.
      actual_default_seed = MaxLfsrDw'(i_prim_lfsr.DefaultSeedLocal);

      // enable this LFSR
      lfsr_en[k] = 1;

      $display("Starting LFSR maxlen test for width %0d: running %0d cycles", k, 2 ** k - 1);
      for (longint unsigned i = 0; i <= lfsr_periods[MaxLfsrDw] && lfsr_en[k]; i++) begin
        main_clk.wait_clks(1);
        // Check if we reached the initial state again.
        if (state_out[k] == actual_default_seed && lfsr_en[k]) begin
          lfsr_en[k] = 1'b0;
          // We expect this to occur only after the maximum length period.
          if (i == lfsr_periods[k]) begin
            $display("LFSR maxlen test for width %0d passed!", k);
          end else begin
            $error("LFSR maxlen test for width %0d failed at period %0d!", k, i);
            err[k] = 1'b1;
          end
        end
      end

      main_clk.wait_clks(10);
      if (lfsr_en[k]) begin
        $error("LFSR with width %0d never got back to the initial state!", k);
        err[k] = 1'b1;
      end

      ////////////////////////////////
      // Random Vectors
      ////////////////////////////////

      // Load an invalid seed externally to trigger the lockup condition.
      lfsr_en[k] = 1;

      // Add some additional toggles for coverage - checking is done within the module using SVAs.
      repeat ($urandom_range(5000, 10000)) begin
        // Do random reset sometimes
        if ($urandom_range(0, 10) == 0) main_clk.apply_reset();
        randomize(rand_seed);
        randomize(rand_entropy);
        seed[k] = rand_seed;
        entropy[k] = rand_entropy;
        lfsr_en[k] = $urandom_range(0, 1);
        seed_en[k] = $urandom_range(0, 1);
        main_clk.wait_clks(1);
      end

      ////////////////////////////////
      // Lockup Check
      ////////////////////////////////

      lfsr_en[k] = 0;
      seed_en[k] = 0;
      seed[k] = 0;
      entropy[k] = 0;

      // Wait a few cycles
      main_clk.wait_clks(10);

      // Load an invalid seed externally to trigger the lockup condition.
      lfsr_en[k] = 1;
      seed_en[k] = 1;

      if (LfsrType == "GAL_XOR") begin
        seed[k] = {k{1'b0}};
      end else begin // "FIB_XNOR"
        seed[k] = {k{1'b1}};
      end

       main_clk.wait_clks(1);

       // cover the case where the LFSR is disabled for a cycle.
       lfsr_en[k] = 0;
       seed_en[k] = 0;
       seed[k] = 0;

      if (gen_duts[k].i_prim_lfsr.lockup) begin
        $display("LFSR with width %0d detected lockup condition!", k);
      end else begin
        $error("LFSR with width %0d does not detect lockup condition", k);
        err[k] = 1'b1;
      end

      main_clk.wait_clks(1);
      lfsr_en[k] = 1;
      main_clk.wait_clks(1);

      // we expect that the LFSR returns to its initial state
      if (gen_duts[k].i_prim_lfsr.lfsr_q == actual_default_seed) begin
        $display("LFSR lockup test for width %0d passed!", k);
      end else begin
        $error("LFSR with width %0d does not reset to DefaultSeedLocal when lockup is detected", k);
        err[k] = 1'b1;
      end

      lfsr_en[k] = 0;
      main_clk.wait_clks(10);

      main_clk.stop_clk();
      test_done[k] = 1;
    end
  end

  initial begin
    $display("Testing LFSR of type %0s for widths {[%0d:%0d]}", LfsrType, MinLfsrDw, MaxLfsrDw);
    `DV_WAIT(test_done === '1, , 1_000_000_000 /*1ms*/, "prim_lfsr_tb")
    dv_test_status_pkg::dv_test_status(.passed(err === '0 && test_done === '1));
    $finish();
  end

  // TODO: perhaps wrap this in a macro?
  initial begin
    bit poll_for_stop;
    int unsigned poll_for_stop_interval_ns;

    poll_for_stop = 1'b1;
    void'($value$plusargs("poll_for_stop=%0b", poll_for_stop));
    poll_for_stop_interval_ns = 1000;
    void'($value$plusargs("poll_for_stop_interval_ns=%0d", poll_for_stop_interval_ns));
    if (poll_for_stop) dv_utils_pkg::poll_for_stop(.interval_ns(poll_for_stop_interval_ns));
  end

endmodule : prim_lfsr_tb
