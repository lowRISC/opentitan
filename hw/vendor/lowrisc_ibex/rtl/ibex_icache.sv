// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Instruction cache
 *
 * Provides an instruction cache along with cache management, instruction buffering and prefetching
 */

`include "prim_assert.sv"

module ibex_icache #(
  parameter bit          BranchPredictor = 1'b0,
  // Cache arrangement parameters
  parameter int unsigned BusWidth        = 32,
  parameter int unsigned CacheSizeBytes  = 4*1024,
  parameter bit          ICacheECC       = 1'b0,
  parameter int unsigned LineSize        = 64,
  parameter int unsigned NumWays         = 2,
  // Only cache branch targets
  parameter bit          BranchCache     = 1'b0
) (
    // Clock and reset
    input  logic                clk_i,
    input  logic                rst_ni,

    // Signal that the core would like instructions
    input  logic                req_i,

    // Set the cache's address counter
    input  logic                branch_i,
    input  logic                branch_spec_i,
    input  logic                predicted_branch_i,
    input  logic                branch_mispredict_i,
    input  logic [31:0]         addr_i,

    // IF stage interface: Pass fetched instructions to the core
    input  logic                ready_i,
    output logic                valid_o,
    output logic [31:0]         rdata_o,
    output logic [31:0]         addr_o,
    output logic                err_o,
    output logic                err_plus2_o,

    // Instruction memory / interconnect interface: Fetch instruction data from memory
    output logic                instr_req_o,
    input  logic                instr_gnt_i,
    output logic [31:0]         instr_addr_o,
    input  logic [BusWidth-1:0] instr_rdata_i,
    input  logic                instr_err_i,
    input  logic                instr_pmp_err_i,
    input  logic                instr_rvalid_i,

    // Cache status
    input  logic                icache_enable_i,
    input  logic                icache_inval_i,
    output logic                busy_o
);
  // Local constants
  localparam int unsigned ADDR_W       = 32;
  // Number of fill buffers (must be >= 2)
  localparam int unsigned NUM_FB       = 4;
  // Request throttling threshold
  localparam int unsigned FB_THRESHOLD = NUM_FB - 2;
  // Derived parameters
  localparam int unsigned LINE_SIZE_ECC   = ICacheECC ? (LineSize + 8) : LineSize;
  localparam int unsigned LINE_SIZE_BYTES = LineSize/8;
  localparam int unsigned LINE_W          = $clog2(LINE_SIZE_BYTES);
  localparam int unsigned BUS_BYTES       = BusWidth/8;
  localparam int unsigned BUS_W           = $clog2(BUS_BYTES);
  localparam int unsigned LINE_BEATS      = LINE_SIZE_BYTES / BUS_BYTES;
  localparam int unsigned LINE_BEATS_W    = $clog2(LINE_BEATS);
  localparam int unsigned NUM_LINES       = CacheSizeBytes / NumWays / LINE_SIZE_BYTES;
  localparam int unsigned INDEX_W         = $clog2(NUM_LINES);
  localparam int unsigned INDEX_HI        = INDEX_W + LINE_W - 1;
  localparam int unsigned TAG_SIZE        = ADDR_W - INDEX_W - LINE_W + 1; // 1 valid bit
  localparam int unsigned TAG_SIZE_ECC    = ICacheECC ? (TAG_SIZE + 6) : TAG_SIZE;
  localparam int unsigned OUTPUT_BEATS    = (BUS_BYTES / 2); // number of halfwords

  // Prefetch signals
  logic [ADDR_W-1:0]                   lookup_addr_aligned;
  logic [ADDR_W-1:0]                   branch_mispredict_addr;
  logic [ADDR_W-1:0]                   prefetch_addr_d, prefetch_addr_q;
  logic                                prefetch_addr_en;
  logic                                branch_or_mispredict;
  // Cache pipelipe IC0 signals
  logic                                branch_suppress;
  logic                                lookup_throttle;
  logic                                lookup_req_ic0;
  logic [ADDR_W-1:0]                   lookup_addr_ic0;
  logic [INDEX_W-1:0]                  lookup_index_ic0;
  logic                                fill_req_ic0;
  logic [INDEX_W-1:0]                  fill_index_ic0;
  logic [TAG_SIZE-1:0]                 fill_tag_ic0;
  logic [LineSize-1:0]                 fill_wdata_ic0;
  logic                                lookup_grant_ic0;
  logic                                lookup_actual_ic0;
  logic                                fill_grant_ic0;
  logic                                tag_req_ic0;
  logic [INDEX_W-1:0]                  tag_index_ic0;
  logic [NumWays-1:0]                  tag_banks_ic0;
  logic                                tag_write_ic0;
  logic [TAG_SIZE_ECC-1:0]             tag_wdata_ic0;
  logic                                data_req_ic0;
  logic [INDEX_W-1:0]                  data_index_ic0;
  logic [NumWays-1:0]                  data_banks_ic0;
  logic                                data_write_ic0;
  logic [LINE_SIZE_ECC-1:0]            data_wdata_ic0;
  // Cache pipelipe IC1 signals
  logic [TAG_SIZE_ECC-1:0]             tag_rdata_ic1  [NumWays];
  logic [LINE_SIZE_ECC-1:0]            data_rdata_ic1 [NumWays];
  logic [LINE_SIZE_ECC-1:0]            hit_data_ic1;
  logic                                lookup_valid_ic1;
  logic [ADDR_W-1:INDEX_HI+1]          lookup_addr_ic1;
  logic [NumWays-1:0]                  tag_match_ic1;
  logic                                tag_hit_ic1;
  logic [NumWays-1:0]                  tag_invalid_ic1;
  logic [NumWays-1:0]                  lowest_invalid_way_ic1;
  logic [NumWays-1:0]                  round_robin_way_ic1, round_robin_way_q;
  logic [NumWays-1:0]                  sel_way_ic1;
  logic                                ecc_err_ic1;
  logic                                ecc_write_req;
  logic [NumWays-1:0]                  ecc_write_ways;
  logic [INDEX_W-1:0]                  ecc_write_index;
  // Fill buffer signals
  logic                                gnt_or_pmp_err, gnt_not_pmp_err;
  logic [$clog2(NUM_FB)-1:0]           fb_fill_level;
  logic                                fill_cache_new;
  logic                                fill_new_alloc;
  logic                                fill_spec_req, fill_spec_done, fill_spec_hold;
  logic [NUM_FB-1:0][NUM_FB-1:0]       fill_older_d, fill_older_q;
  logic [NUM_FB-1:0]                   fill_alloc_sel, fill_alloc;
  logic [NUM_FB-1:0]                   fill_busy_d, fill_busy_q;
  logic [NUM_FB-1:0]                   fill_done;
  logic [NUM_FB-1:0]                   fill_in_ic1;
  logic [NUM_FB-1:0]                   fill_stale_d, fill_stale_q;
  logic [NUM_FB-1:0]                   fill_cache_d, fill_cache_q;
  logic [NUM_FB-1:0]                   fill_hit_ic1, fill_hit_d, fill_hit_q;
  logic [NUM_FB-1:0][LINE_BEATS_W:0]   fill_ext_cnt_d, fill_ext_cnt_q;
  logic [NUM_FB-1:0]                   fill_ext_hold_d, fill_ext_hold_q;
  logic [NUM_FB-1:0]                   fill_ext_done_d, fill_ext_done_q;
  logic [NUM_FB-1:0][LINE_BEATS_W:0]   fill_rvd_cnt_d, fill_rvd_cnt_q;
  logic [NUM_FB-1:0]                   fill_rvd_done;
  logic [NUM_FB-1:0]                   fill_ram_done_d, fill_ram_done_q;
  logic [NUM_FB-1:0]                   fill_out_grant;
  logic [NUM_FB-1:0][LINE_BEATS_W:0]   fill_out_cnt_d, fill_out_cnt_q;
  logic [NUM_FB-1:0]                   fill_out_done;
  logic [NUM_FB-1:0]                   fill_ext_req, fill_rvd_exp, fill_ram_req, fill_out_req;
  logic [NUM_FB-1:0]                   fill_data_sel, fill_data_reg, fill_data_hit, fill_data_rvd;
  logic [NUM_FB-1:0][LINE_BEATS_W-1:0] fill_ext_off, fill_rvd_off;
  logic [NUM_FB-1:0][LINE_BEATS_W:0]   fill_ext_beat, fill_rvd_beat;
  logic [NUM_FB-1:0]                   fill_ext_arb, fill_ram_arb, fill_out_arb;
  logic [NUM_FB-1:0]                   fill_rvd_arb;
  logic [NUM_FB-1:0]                   fill_entry_en;
  logic [NUM_FB-1:0]                   fill_addr_en;
  logic [NUM_FB-1:0]                   fill_way_en;
  logic [NUM_FB-1:0][LINE_BEATS-1:0]   fill_data_en;
  logic [NUM_FB-1:0][LINE_BEATS-1:0]   fill_err_d, fill_err_q;
  logic [ADDR_W-1:0]                   fill_addr_q [NUM_FB];
  logic [NumWays-1:0]                  fill_way_q  [NUM_FB];
  logic [LineSize-1:0]                 fill_data_d [NUM_FB];
  logic [LineSize-1:0]                 fill_data_q [NUM_FB];
  logic [ADDR_W-1:BUS_W]               fill_ext_req_addr;
  logic [ADDR_W-1:0]                   fill_ram_req_addr;
  logic [NumWays-1:0]                  fill_ram_req_way;
  logic [LineSize-1:0]                 fill_ram_req_data;
  logic [LineSize-1:0]                 fill_out_data;
  logic [LINE_BEATS-1:0]               fill_out_err;
  // External req signals
  logic                                instr_req;
  logic [ADDR_W-1:BUS_W]               instr_addr;
  // Data output signals
  logic                                skid_complete_instr;
  logic                                skid_ready;
  logic                                output_compressed;
  logic                                skid_valid_d, skid_valid_q, skid_en;
  logic [15:0]                         skid_data_d, skid_data_q;
  logic                                skid_err_q;
  logic                                output_valid;
  logic                                addr_incr_two;
  logic                                output_addr_en;
  logic [ADDR_W-1:1]                   output_addr_incr;
  logic [ADDR_W-1:1]                   output_addr_d, output_addr_q;
  logic [15:0]                         output_data_lo, output_data_hi;
  logic                                data_valid, output_ready;
  logic [LineSize-1:0]                 line_data;
  logic [LINE_BEATS-1:0]               line_err;
  logic [31:0]                         line_data_muxed;
  logic                                line_err_muxed;
  logic [31:0]                         output_data;
  logic                                output_err;
  // Invalidations
  logic                                start_inval, inval_done;
  logic                                reset_inval_q;
  logic                                inval_prog_d, inval_prog_q;
  logic [INDEX_W-1:0]                  inval_index_d, inval_index_q;

  //////////////////////////
  // Instruction prefetch //
  //////////////////////////

  if (BranchPredictor) begin : g_branch_predictor
    // Where the branch predictor is present record what address followed a predicted branch.  If
    // that branch is predicted taken but mispredicted (so not-taken) this is used to resume on
    // the not-taken code path.
    logic [31:0] branch_mispredict_addr_q;
    logic        branch_mispredict_addr_en;

    assign branch_mispredict_addr_en = branch_i & predicted_branch_i;

    always_ff @(posedge clk_i) begin
      if (branch_mispredict_addr_en) begin
        branch_mispredict_addr_q <= {output_addr_incr, 1'b0};
      end
    end

    assign branch_mispredict_addr = branch_mispredict_addr_q;

  end else begin : g_no_branch_predictor
    logic        unused_predicted_branch;

    assign unused_predicted_branch   = predicted_branch_i;

    assign branch_mispredict_addr = '0;
  end

  assign branch_or_mispredict = branch_i | branch_mispredict_i;

  assign lookup_addr_aligned = {lookup_addr_ic0[ADDR_W-1:LINE_W],{LINE_W{1'b0}}};

  // The prefetch address increments by one cache line for each granted request.
  // This address is also updated if there is a branch that is not granted, since the target
  // address (addr_i) is only valid for one cycle while branch_i is high.

  // The captured branch target address is not forced to be aligned since the offset in the cache
  // line must also be recorded for later use by the fill buffers.
  assign prefetch_addr_d     =
      lookup_grant_ic0 ? (lookup_addr_aligned + {{ADDR_W-LINE_W-1{1'b0}},1'b1,{LINE_W{1'b0}}}) :
      branch_i         ? addr_i :
                         branch_mispredict_addr;

  assign prefetch_addr_en    = branch_or_mispredict | lookup_grant_ic0;

  always_ff @(posedge clk_i) begin
    if (prefetch_addr_en) begin
      prefetch_addr_q <= prefetch_addr_d;
    end
  end

  ////////////////////////
  // Pipeline stage IC0 //
  ////////////////////////

  // Cache lookup
  assign lookup_throttle  = (fb_fill_level > FB_THRESHOLD[$clog2(NUM_FB)-1:0]);

  assign lookup_req_ic0   = req_i & ~&fill_busy_q & (branch_or_mispredict | ~lookup_throttle) &
                            ~ecc_write_req;
  assign lookup_addr_ic0  = branch_spec_i       ? addr_i :
                            branch_mispredict_i ? branch_mispredict_addr :
                                                  prefetch_addr_q;
  assign lookup_index_ic0 = lookup_addr_ic0[INDEX_HI:LINE_W];

  // Cache write
  assign fill_req_ic0   = (|fill_ram_req);
  assign fill_index_ic0 = fill_ram_req_addr[INDEX_HI:LINE_W];
  assign fill_tag_ic0   = {(~inval_prog_q & ~ecc_write_req),fill_ram_req_addr[ADDR_W-1:INDEX_HI+1]};
  assign fill_wdata_ic0 = fill_ram_req_data;

  // Suppress a new lookup on a not-taken branch (as the address will be incorrect)
  assign branch_suppress   = branch_spec_i & ~branch_i;

  // Arbitrated signals - lookups have highest priority
  assign lookup_grant_ic0  = lookup_req_ic0 & ~branch_suppress;
  assign fill_grant_ic0    = fill_req_ic0 & (~lookup_req_ic0 | branch_suppress) & ~inval_prog_q &
                             ~ecc_write_req;
  // Qualified lookup grant to mask ram signals in IC1 if access was not made
  assign lookup_actual_ic0 = lookup_grant_ic0 & icache_enable_i & ~inval_prog_q & ~start_inval;

  // Tagram
  assign tag_req_ic0   = lookup_req_ic0 | fill_req_ic0 | inval_prog_q | ecc_write_req;
  assign tag_index_ic0 = inval_prog_q   ? inval_index_q :
                         ecc_write_req  ? ecc_write_index :
                         fill_grant_ic0 ? fill_index_ic0 :
                                          lookup_index_ic0;
  assign tag_banks_ic0 = ecc_write_req  ? ecc_write_ways :
                         fill_grant_ic0 ? fill_ram_req_way :
                                          {NumWays{1'b1}};
  assign tag_write_ic0 = fill_grant_ic0 | inval_prog_q | ecc_write_req;

  // Dataram
  assign data_req_ic0   = lookup_req_ic0 | fill_req_ic0;
  assign data_index_ic0 = tag_index_ic0;
  assign data_banks_ic0 = tag_banks_ic0;
  assign data_write_ic0 = tag_write_ic0;

  // Append ECC checkbits to write data if required
  if (ICacheECC) begin : gen_ecc_wdata

    // Tagram ECC
    // Reuse the same ecc encoding module for larger cache sizes by padding with zeros
    logic [21:0]          tag_ecc_input_padded;
    logic [27:0]          tag_ecc_output_padded;
    logic [22-TAG_SIZE:0] tag_ecc_output_unused;

    assign tag_ecc_input_padded  = {{22-TAG_SIZE{1'b0}},fill_tag_ic0};
    assign tag_ecc_output_unused = tag_ecc_output_padded[21:TAG_SIZE-1];

    prim_secded_28_22_enc tag_ecc_enc (
      .in  (tag_ecc_input_padded),
      .out (tag_ecc_output_padded)
    );

    assign tag_wdata_ic0 = {tag_ecc_output_padded[27:22],tag_ecc_output_padded[TAG_SIZE-1:0]};

    // Dataram ECC
    prim_secded_72_64_enc data_ecc_enc (
      .in  (fill_wdata_ic0),
      .out (data_wdata_ic0)
    );

  end else begin : gen_noecc_wdata
    assign tag_wdata_ic0  = fill_tag_ic0;
    assign data_wdata_ic0 = fill_wdata_ic0;
  end

  ////////////////
  // IC0 -> IC1 //
  ////////////////

  for (genvar way = 0; way < NumWays; way++) begin : gen_rams
    // Tag RAM instantiation
    prim_ram_1p #(
      .Width           (TAG_SIZE_ECC),
      .Depth           (NUM_LINES),
      .DataBitsPerMask (TAG_SIZE_ECC)
    ) tag_bank (
      .clk_i    (clk_i),
      .req_i    (tag_req_ic0 & tag_banks_ic0[way]),
      .write_i  (tag_write_ic0),
      .wmask_i  ({TAG_SIZE_ECC{1'b1}}),
      .addr_i   (tag_index_ic0),
      .wdata_i  (tag_wdata_ic0),
      .rdata_o  (tag_rdata_ic1[way])
    );
    // Data RAM instantiation
    prim_ram_1p #(
      .Width           (LINE_SIZE_ECC),
      .Depth           (NUM_LINES),
      .DataBitsPerMask (LINE_SIZE_ECC)
    ) data_bank (
      .clk_i    (clk_i),
      .req_i    (data_req_ic0 & data_banks_ic0[way]),
      .write_i  (data_write_ic0),
      .wmask_i  ({LINE_SIZE_ECC{1'b1}}),
      .addr_i   (data_index_ic0),
      .wdata_i  (data_wdata_ic0),
      .rdata_o  (data_rdata_ic1[way])
    );
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lookup_valid_ic1 <= 1'b0;
    end else begin
      lookup_valid_ic1 <= lookup_actual_ic0;
    end
  end

  always_ff @(posedge clk_i) begin
    if (lookup_grant_ic0) begin
      lookup_addr_ic1 <= lookup_addr_ic0[ADDR_W-1:INDEX_HI+1];
      fill_in_ic1     <= fill_alloc_sel;
    end
  end

  ////////////////////////
  // Pipeline stage IC1 //
  ////////////////////////

  // Tag matching
  for (genvar way = 0; way < NumWays; way++) begin : gen_tag_match
    assign tag_match_ic1[way]   = (tag_rdata_ic1[way][TAG_SIZE-1:0] ==
                                   {1'b1,lookup_addr_ic1[ADDR_W-1:INDEX_HI+1]});
    assign tag_invalid_ic1[way] = ~tag_rdata_ic1[way][TAG_SIZE-1];
  end

  assign tag_hit_ic1 = |tag_match_ic1;

  // Hit data mux
  always_comb begin
    hit_data_ic1 = 'b0;
    for (int way = 0; way < NumWays; way++) begin
      if (tag_match_ic1[way]) begin
        hit_data_ic1 |= data_rdata_ic1[way];
      end
    end
  end

  // Way selection for allocations to the cache (onehot signals)
  // 1 first invalid way
  // 2 global round-robin (pseudorandom) way
  assign lowest_invalid_way_ic1[0] = tag_invalid_ic1[0];
  assign round_robin_way_ic1[0]    = round_robin_way_q[NumWays-1];
  for (genvar way = 1; way < NumWays; way++) begin : gen_lowest_way
    assign lowest_invalid_way_ic1[way] = tag_invalid_ic1[way] & ~|tag_invalid_ic1[way-1:0];
    assign round_robin_way_ic1[way]    = round_robin_way_q[way-1];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round_robin_way_q <= {{NumWays-1{1'b0}},1'b1};
    end else if (lookup_valid_ic1) begin
      round_robin_way_q <= round_robin_way_ic1;
    end
  end

  assign sel_way_ic1 = |tag_invalid_ic1 ? lowest_invalid_way_ic1 :
                                          round_robin_way_q;

  // ECC checking logic
  if (ICacheECC) begin : gen_data_ecc_checking
    logic [NumWays-1:0] tag_err_ic1;
    logic [1:0]         data_err_ic1;
    logic               ecc_correction_write_d, ecc_correction_write_q;
    logic [NumWays-1:0] ecc_correction_ways_d, ecc_correction_ways_q;
    logic [INDEX_W-1:0] lookup_index_ic1, ecc_correction_index_q;

    // Tag ECC checking
    for (genvar way = 0; way < NumWays; way++) begin : gen_tag_ecc
      logic [1:0]  tag_err_bank_ic1;
      logic [27:0] tag_rdata_padded_ic1;

      // Expand the tag rdata with extra padding if the tag size is less than the maximum
      assign tag_rdata_padded_ic1 = {tag_rdata_ic1[way][TAG_SIZE_ECC-1-:6],
                                     {22-TAG_SIZE{1'b0}},
                                     tag_rdata_ic1[way][TAG_SIZE-1:0]};

      prim_secded_28_22_dec data_ecc_dec (
        .in         (tag_rdata_padded_ic1),
        .d_o        (),
        .syndrome_o (),
        .err_o      (tag_err_bank_ic1)
      );
      assign tag_err_ic1[way] = |tag_err_bank_ic1;
    end

    // Data ECC checking
    // Note - could generate for all ways and mux after
    prim_secded_72_64_dec data_ecc_dec (
      .in         (hit_data_ic1),
      .d_o        (),
      .syndrome_o (),
      .err_o      (data_err_ic1)
    );

    assign ecc_err_ic1 = lookup_valid_ic1 & ((|data_err_ic1) | (|tag_err_ic1));

    // Error correction
    // All ways will be invalidated on a tag error to prevent X-propagation from data_err_ic1 on
    // spurious hits. Also prevents the same line being allocated twice when there was a true
    // hit and a spurious hit.
    assign ecc_correction_ways_d  = {NumWays{|tag_err_ic1}} |
                                    (tag_match_ic1 & {NumWays{|data_err_ic1}});
    assign ecc_correction_write_d = ecc_err_ic1;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        ecc_correction_write_q <= 1'b0;
      end else begin
        ecc_correction_write_q <= ecc_correction_write_d;
      end
    end

    // The index is required in IC1 only when ECC is configured so is registered here
    always_ff @(posedge clk_i) begin
      if (lookup_grant_ic0) begin
        lookup_index_ic1 <= lookup_addr_ic0[INDEX_HI-:INDEX_W];
      end
    end

    // Store the ways with errors to be invalidated
    always_ff @(posedge clk_i) begin
      if (ecc_err_ic1) begin
        ecc_correction_ways_q  <= ecc_correction_ways_d;
        ecc_correction_index_q <= lookup_index_ic1;
      end
    end

    assign ecc_write_req   = ecc_correction_write_q;
    assign ecc_write_ways  = ecc_correction_ways_q;
    assign ecc_write_index = ecc_correction_index_q;

  end else begin : gen_no_data_ecc
    assign ecc_err_ic1     = 1'b0;
    assign ecc_write_req   = 1'b0;
    assign ecc_write_ways  = '0;
    assign ecc_write_index = '0;
  end

  ///////////////////////////////
  // Cache allocation decision //
  ///////////////////////////////

  if (BranchCache) begin : gen_caching_logic

    // Cache branch target + a number of subsequent lines
    localparam int unsigned CACHE_AHEAD = 2;
    localparam int unsigned CACHE_CNT_W = (CACHE_AHEAD == 1) ? 1 : $clog2(CACHE_AHEAD) + 1;
    logic                   cache_cnt_dec;
    logic [CACHE_CNT_W-1:0] cache_cnt_d, cache_cnt_q;

    assign cache_cnt_dec = lookup_grant_ic0 & (|cache_cnt_q);
    assign cache_cnt_d   = branch_i ? CACHE_AHEAD[CACHE_CNT_W-1:0] :
                                      (cache_cnt_q - {{CACHE_CNT_W-1{1'b0}},cache_cnt_dec});

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cache_cnt_q <= '0;
      end else begin
        cache_cnt_q <= cache_cnt_d;
      end
    end

    assign fill_cache_new = (branch_i | (|cache_cnt_q)) & icache_enable_i &
                            ~icache_inval_i & ~inval_prog_q;

  end else begin : gen_cache_all

    // Cache all missing fetches
    assign fill_cache_new = icache_enable_i & ~start_inval & ~inval_prog_q;
  end

  //////////////////////////
  // Fill buffer tracking //
  //////////////////////////

  always_comb begin
    fb_fill_level = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_busy_q[i] & ~fill_stale_q[i]) begin
        fb_fill_level += {{$clog2(NUM_FB)-1{1'b0}},1'b1};
      end
    end
  end

  // PMP errors might not / don't need to be granted (since the external request is masked)
  assign gnt_or_pmp_err  = instr_gnt_i | instr_pmp_err_i;
  assign gnt_not_pmp_err = instr_gnt_i & ~instr_pmp_err_i;
  // Allocate a new buffer for every granted lookup
  assign fill_new_alloc = lookup_grant_ic0;
  // Track whether a speculative external request was made from IC0, and whether it was granted
  // Speculative requests are only made for branches, or if the cache is disabled
  assign fill_spec_req  = (~icache_enable_i | branch_or_mispredict) & ~|fill_ext_req;
  assign fill_spec_done = fill_spec_req & gnt_not_pmp_err;
  assign fill_spec_hold = fill_spec_req & ~gnt_or_pmp_err;

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : gen_fbs

    /////////////////////////////
    // Fill buffer allocations //
    /////////////////////////////

    // Allocate the lowest available buffer
    if (fb == 0) begin : gen_fb_zero
      assign fill_alloc_sel[fb] = ~fill_busy_q[fb];
    end else begin : gen_fb_rest
      assign fill_alloc_sel[fb] = ~fill_busy_q[fb] & (&fill_busy_q[fb-1:0]);
    end

    assign fill_alloc[fb]      = fill_alloc_sel[fb] & fill_new_alloc;
    assign fill_busy_d[fb]     = fill_alloc[fb] | (fill_busy_q[fb] & ~fill_done[fb]);

    // Track which other fill buffers are older than this one (for age-based arbitration)
    // TODO sparsify
    assign fill_older_d[fb]    = (fill_alloc[fb] ? fill_busy_q : fill_older_q[fb]) & ~fill_done;

    // A fill buffer can release once all its actions are completed
                                 // all data written to the cache (unless hit or error)
    assign fill_done[fb]       = (fill_ram_done_q[fb] | fill_hit_q[fb] | ~fill_cache_q[fb] |
                                  (|fill_err_q[fb])) &
                                 // all data output unless stale due to intervening branch
                                 (fill_out_done[fb] | fill_stale_q[fb] | branch_or_mispredict) &
                                 // all external requests completed
                                 fill_rvd_done[fb];

    /////////////////////////////////
    // Fill buffer status tracking //
    /////////////////////////////////

    // Track staleness (requests become stale when a branch intervenes)
    assign fill_stale_d[fb]    = fill_busy_q[fb] & (branch_or_mispredict | fill_stale_q[fb]);
    // Track whether or not this request should allocate to the cache
    // Any invalidation or disabling of the cache while the buffer is busy will stop allocation
    assign fill_cache_d[fb]    = (fill_alloc[fb] & fill_cache_new) |
                                 (fill_cache_q[fb] & fill_busy_q[fb] &
                                  icache_enable_i & ~icache_inval_i);
    // Record whether the request hit in the cache
    assign fill_hit_ic1[fb]    = lookup_valid_ic1 & fill_in_ic1[fb] & tag_hit_ic1 & ~ecc_err_ic1;
    assign fill_hit_d[fb]      = fill_hit_ic1[fb] | (fill_hit_q[fb] & fill_busy_q[fb]);

    ///////////////////////////////////////////
    // Fill buffer external request tracking //
    ///////////////////////////////////////////

    // Make an external request
    assign fill_ext_req[fb]    = fill_busy_q[fb] & ~fill_ext_done_d[fb];

    // Count the number of completed external requests (each line requires LINE_BEATS requests)
    // Don't count fake PMP error grants here since they will never receive an rvalid response
    assign fill_ext_cnt_d[fb]  = fill_alloc[fb] ?
                                   {{LINE_BEATS_W{1'b0}},fill_spec_done} :
                                   (fill_ext_cnt_q[fb] + {{LINE_BEATS_W{1'b0}},
                                                          fill_ext_arb[fb] & gnt_not_pmp_err});
    // External request must be held until granted
    assign fill_ext_hold_d[fb] = (fill_alloc[fb] & fill_spec_hold) |
                                 (fill_ext_arb[fb] & ~gnt_or_pmp_err);
    // External requests are completed when the counter is filled or when the request is cancelled
    assign fill_ext_done_d[fb] = (fill_ext_cnt_q[fb][LINE_BEATS_W] |
                                  // external requests are considered complete if the request hit
                                  fill_hit_ic1[fb] | fill_hit_q[fb] |
                                  // external requests will stop once any PMP error is received
                                  fill_err_q[fb][fill_ext_off[fb]] |
                                  // cancel if the line won't be cached and, it is stale
                                  (~fill_cache_q[fb] & (branch_or_mispredict | fill_stale_q[fb] |
                                   // or we're already at the end of the line
                                                        fill_ext_beat[fb][LINE_BEATS_W]))) &
                                 // can't cancel while we are waiting for a grant on the bus
                                 ~fill_ext_hold_q[fb] & fill_busy_q[fb];
    // Track whether this fill buffer expects to receive beats of data
    assign fill_rvd_exp[fb]    = fill_busy_q[fb] & ~fill_rvd_done[fb];
    // Count the number of rvalid beats received
    assign fill_rvd_cnt_d[fb]  = fill_alloc[fb] ? '0 :
                                                  (fill_rvd_cnt_q[fb] +
                                                   {{LINE_BEATS_W{1'b0}},fill_rvd_arb[fb]});
    // External data is complete when all issued external requests have received their data
    assign fill_rvd_done[fb]   = (fill_ext_done_q[fb] & ~fill_ext_hold_q[fb]) &
                                 (fill_rvd_cnt_q[fb] == fill_ext_cnt_q[fb]);

    //////////////////////////////////////
    // Fill buffer data output tracking //
    //////////////////////////////////////

    // Send data to the IF stage for requests that are not stale, have not completed their
    // data output, and have data available to send.
    // Data is available if:
    // - The request hit in the cache
    // - The current beat is an error (since a PMP error might not actually receive any data)
    // - Buffered data is available (fill_rvd_cnt_q is ahead of fill_out_cnt_q)
    // - Data is available from the bus this cycle (fill_rvd_arb)
    assign fill_out_req[fb]    = fill_busy_q[fb] & ~fill_stale_q[fb] & ~fill_out_done[fb] &
                                 (fill_hit_ic1[fb] | fill_hit_q[fb] |
                                  (fill_err_q[fb][fill_out_cnt_q[fb][LINE_BEATS_W-1:0]]) |
                                  (fill_rvd_beat[fb] > fill_out_cnt_q[fb]) | fill_rvd_arb[fb]);

    // Calculate when a beat of data is output. Any ECC error squashes the output that cycle.
    assign fill_out_grant[fb]  = fill_out_arb[fb] & output_ready;

    // Count the beats of data output to the IF stage
    assign fill_out_cnt_d[fb]  = fill_alloc[fb] ? {1'b0,lookup_addr_ic0[LINE_W-1:BUS_W]} :
                                                  (fill_out_cnt_q[fb] +
                                                   {{LINE_BEATS_W{1'b0}},fill_out_grant[fb]});
    // Data output complete when the counter fills
    assign fill_out_done[fb]   = fill_out_cnt_q[fb][LINE_BEATS_W];

    //////////////////////////////////////
    // Fill buffer ram request tracking //
    //////////////////////////////////////

                                 // make a fill request once all data beats received
    assign fill_ram_req[fb]    = fill_busy_q[fb] & fill_rvd_cnt_q[fb][LINE_BEATS_W] &
                                 // unless the request hit, was non-allocating or got an error
                                 ~fill_hit_q[fb] & fill_cache_q[fb] & ~|fill_err_q[fb] &
                                 // or the request was already completed
                                 ~fill_ram_done_q[fb];

    // Record when a cache allocation request has been completed
    assign fill_ram_done_d[fb] = fill_ram_arb[fb] | (fill_ram_done_q[fb] & fill_busy_q[fb]);

    //////////////////////////////
    // Fill buffer line offsets //
    //////////////////////////////

    // When we branch into the middle of a line, the output count will not start from zero. This
    // beat count is used to know which incoming rdata beats are relevant.
    assign fill_ext_beat[fb]   = {1'b0,fill_addr_q[fb][LINE_W-1:BUS_W]} +
                                 fill_ext_cnt_q[fb][LINE_BEATS_W:0];
    assign fill_ext_off[fb]    = fill_ext_beat[fb][LINE_BEATS_W-1:0];
    assign fill_rvd_beat[fb]   = {1'b0,fill_addr_q[fb][LINE_W-1:BUS_W]} +
                                 fill_rvd_cnt_q[fb][LINE_BEATS_W:0];
    assign fill_rvd_off[fb]    = fill_rvd_beat[fb][LINE_BEATS_W-1:0];

    /////////////////////////////
    // Fill buffer arbitration //
    /////////////////////////////

    // Age based arbitration - all these signals are one-hot
    assign fill_ext_arb[fb]    = fill_ext_req[fb] & ~|(fill_ext_req & fill_older_q[fb]);
    assign fill_ram_arb[fb]    = fill_ram_req[fb] & fill_grant_ic0 & ~|(fill_ram_req & fill_older_q[fb]);
    // Calculate which fill buffer is the oldest one which still needs to output data to IF
    assign fill_data_sel[fb]   = ~|(fill_busy_q & ~fill_out_done & ~fill_stale_q &
                                    fill_older_q[fb]);
    // Arbitrate the request which has data available to send, and is the oldest outstanding
    assign fill_out_arb[fb]    = fill_out_req[fb] & fill_data_sel[fb];
    // Assign incoming rvalid data to the oldest fill buffer expecting it
    assign fill_rvd_arb[fb]    = instr_rvalid_i & fill_rvd_exp[fb] & ~|(fill_rvd_exp & fill_older_q[fb]);

    /////////////////////////////
    // Fill buffer data muxing //
    /////////////////////////////

    // Output data muxing controls
    // 1. Select data from the fill buffer data register
    assign fill_data_reg[fb]   = fill_busy_q[fb] & ~fill_stale_q[fb] &
                                 ~fill_out_done[fb] & fill_data_sel[fb] &
    //                           The incoming data is already ahead of the output count
                                 ((fill_rvd_beat[fb] > fill_out_cnt_q[fb]) | fill_hit_q[fb] |
                                  (|fill_err_q[fb]));
    // 2. Select IC1 hit data
    assign fill_data_hit[fb]   = fill_busy_q[fb] & fill_hit_ic1[fb] & fill_data_sel[fb];
    // 3. Select incoming instr_rdata_i
    assign fill_data_rvd[fb]   = fill_busy_q[fb] & fill_rvd_arb[fb] & ~fill_hit_q[fb] &
                                 ~fill_hit_ic1[fb] & ~fill_stale_q[fb] & ~fill_out_done[fb] &
    //                           The incoming data lines up with the output count
                                 (fill_rvd_beat[fb] == fill_out_cnt_q[fb]) & fill_data_sel[fb];


    ///////////////////////////
    // Fill buffer registers //
    ///////////////////////////

    // Fill buffer general enable
    assign fill_entry_en[fb]   = fill_alloc[fb] | fill_busy_q[fb];

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fill_busy_q[fb]     <= 1'b0;
        fill_older_q[fb]    <= '0;
        fill_stale_q[fb]    <= 1'b0;
        fill_cache_q[fb]    <= 1'b0;
        fill_hit_q[fb]      <= 1'b0;
        fill_ext_cnt_q[fb]  <= '0;
        fill_ext_hold_q[fb] <= 1'b0;
        fill_ext_done_q[fb] <= 1'b0;
        fill_rvd_cnt_q[fb]  <= '0;
        fill_ram_done_q[fb] <= 1'b0;
        fill_out_cnt_q[fb]  <= '0;
      end else if (fill_entry_en[fb]) begin
        fill_busy_q[fb]     <= fill_busy_d[fb];
        fill_older_q[fb]    <= fill_older_d[fb];
        fill_stale_q[fb]    <= fill_stale_d[fb];
        fill_cache_q[fb]    <= fill_cache_d[fb];
        fill_hit_q[fb]      <= fill_hit_d[fb];
        fill_ext_cnt_q[fb]  <= fill_ext_cnt_d[fb];
        fill_ext_hold_q[fb] <= fill_ext_hold_d[fb];
        fill_ext_done_q[fb] <= fill_ext_done_d[fb];
        fill_rvd_cnt_q[fb]  <= fill_rvd_cnt_d[fb];
        fill_ram_done_q[fb] <= fill_ram_done_d[fb];
        fill_out_cnt_q[fb]  <= fill_out_cnt_d[fb];
      end
    end

    ////////////////////////////////////////
    // Fill buffer address / data storage //
    ////////////////////////////////////////

    assign fill_addr_en[fb]    = fill_alloc[fb];
    assign fill_way_en[fb]     = (lookup_valid_ic1 & fill_in_ic1[fb]);

    always_ff @(posedge clk_i) begin
      if (fill_addr_en[fb]) begin
        fill_addr_q[fb] <= lookup_addr_ic0;
      end
    end

    always_ff @(posedge clk_i) begin
      if (fill_way_en[fb]) begin
        fill_way_q[fb]  <= sel_way_ic1;
      end
    end

    // Data either comes from the cache or the bus. If there was an ECC error, we must take
    // the incoming bus data since the cache hit data is corrupted.
    assign fill_data_d[fb] = fill_hit_ic1[fb] ? hit_data_ic1[LineSize-1:0] :
                                                {LINE_BEATS{instr_rdata_i}};

    for (genvar b = 0; b < LINE_BEATS; b++) begin : gen_data_buf
      // Error tracking (per beat)
      //                           Either a PMP error on a speculative request,
      assign fill_err_d[fb][b]   = (instr_pmp_err_i & fill_alloc[fb] & fill_spec_req &
                                    (lookup_addr_ic0[LINE_W-1:BUS_W] == b[LINE_BEATS_W-1:0])) |
      //                           a PMP error on a fill buffer ext req
                                   (instr_pmp_err_i & fill_ext_arb[fb] &
                                    (fill_ext_off[fb] == b[LINE_BEATS_W-1:0])) |
      //                           Or a data error with instr_rvalid_i
                                   (fill_rvd_arb[fb] & instr_err_i &
                                    (fill_rvd_off[fb] == b[LINE_BEATS_W-1:0])) |
      //                           Hold the error once recorded
                                   (fill_busy_q[fb] & fill_err_q[fb][b]);

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          fill_err_q[fb][b] <= '0;
        end else if (fill_entry_en[fb]) begin
          fill_err_q[fb][b] <= fill_err_d[fb][b];
        end
      end

      // Enable the relevant part of the data register (or all for cache hits)
      // Ignore incoming rvalid data when we already have cache hit data
      assign fill_data_en[fb][b] = fill_hit_ic1[fb] |
                                   (fill_rvd_arb[fb] & ~fill_hit_q[fb] &
                                    (fill_rvd_off[fb] == b[LINE_BEATS_W-1:0]));

      always_ff @(posedge clk_i) begin
        if (fill_data_en[fb][b]) begin
          fill_data_q[fb][b*BusWidth+:BusWidth] <= fill_data_d[fb][b*BusWidth+:BusWidth];
        end
      end

    end
  end

  ////////////////////////////////
  // Fill buffer one-hot muxing //
  ////////////////////////////////

  // External req info
  always_comb begin
    fill_ext_req_addr = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_ext_arb[i]) begin
        fill_ext_req_addr |= {fill_addr_q[i][ADDR_W-1:LINE_W], fill_ext_off[i]};
      end
    end
  end

  // Cache req info
  always_comb begin
    fill_ram_req_addr = '0;
    fill_ram_req_way  = '0;
    fill_ram_req_data = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_ram_arb[i]) begin
        fill_ram_req_addr |= fill_addr_q[i];
        fill_ram_req_way  |= fill_way_q[i];
        fill_ram_req_data |= fill_data_q[i];
      end
    end
  end

  // IF stage output data
  always_comb begin
    fill_out_data = '0;
    fill_out_err  = '0;
    for (int i = 0; i < NUM_FB; i++) begin
      if (fill_data_reg[i]) begin
        fill_out_data |= fill_data_q[i];
        // Ignore any speculative errors accumulated on cache hits
        fill_out_err  |= (fill_err_q[i] & ~{LINE_BEATS{fill_hit_q[i]}});
      end
    end
  end

  ///////////////////////
  // External requests //
  ///////////////////////

  assign instr_req  = ((~icache_enable_i | branch_or_mispredict) & lookup_grant_ic0) |
                      (|fill_ext_req);

  assign instr_addr = |fill_ext_req ? fill_ext_req_addr :
                                      lookup_addr_ic0[ADDR_W-1:BUS_W];

  assign instr_req_o  = instr_req;
  assign instr_addr_o = {instr_addr[ADDR_W-1:BUS_W],{BUS_W{1'b0}}};

  ////////////////////////
  // Output data muxing //
  ////////////////////////

  // Mux between line-width data sources
  assign line_data = |fill_data_hit ? hit_data_ic1[LineSize-1:0] : fill_out_data;
  assign line_err  = |fill_data_hit ? {LINE_BEATS{1'b0}} : fill_out_err;

  // Mux the relevant beat of line data, based on the output address
  always_comb begin
    line_data_muxed = '0;
    line_err_muxed  = 1'b0;
    for (int i = 0; i < LINE_BEATS; i++) begin
      // When data has been skidded, the output address is behind by one
      if ((output_addr_q[LINE_W-1:BUS_W] + {{LINE_BEATS_W-1{1'b0}},skid_valid_q}) ==
          i[LINE_BEATS_W-1:0]) begin
        line_data_muxed |= line_data[i*32+:32];
        line_err_muxed  |= line_err[i];
      end
    end
  end

  // Mux between incoming rdata and the muxed line data
  assign output_data = |fill_data_rvd ? instr_rdata_i : line_data_muxed;
  assign output_err  = |fill_data_rvd ? instr_err_i   : line_err_muxed;

  // Output data is valid (from any of the three possible sources). Note that fill_out_arb
  // must be used here rather than fill_out_req because data can become valid out of order
  // (e.g. cache hit data can become available ahead of an older outstanding miss).
  assign data_valid = |fill_out_arb;

  // Skid buffer data
  assign skid_data_d = output_data[31:16];

  assign skid_en     = data_valid & (ready_i | skid_ready);

  always_ff @(posedge clk_i) begin
    if (skid_en) begin
      skid_data_q <= skid_data_d;
      skid_err_q  <= output_err;
    end
  end

  // The data in the skid buffer is ready if it's a complete compressed instruction or if there's
  // an error (no need to wait for the second half)
  assign skid_complete_instr = skid_valid_q & ((skid_data_q[1:0] != 2'b11) | skid_err_q);

  // Data can be loaded into the skid buffer for an unaligned uncompressed instruction
  assign skid_ready = output_addr_q[1] & ~skid_valid_q & (~output_compressed | output_err);

  assign output_ready = (ready_i | skid_ready) & ~skid_complete_instr;

  assign output_compressed = (rdata_o[1:0] != 2'b11);

  assign skid_valid_d =
      // Branches invalidate the skid buffer
      branch_or_mispredict ? 1'b0 :
      // Once valid, the skid buffer stays valid until a compressed instruction realigns the stream
      (skid_valid_q ? ~(ready_i & ((skid_data_q[1:0] != 2'b11) | skid_err_q)) :
      // The skid buffer becomes valid when:
                        // - we branch to an unaligned uncompressed instruction
                      (((output_addr_q[1] & (~output_compressed | output_err)) |
                        // - a compressed instruction misaligns the stream
                        (~output_addr_q[1] & output_compressed & ~output_err & ready_i)) & data_valid));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      skid_valid_q <= 1'b0;
    end else begin
      skid_valid_q <= skid_valid_d;
    end
  end

  // Signal that valid data is available to the IF stage
  // Note that if the first half of an unaligned instruction reports an error, we do not need
  // to wait for the second half (and for PMP errors we might not have fetched the second half)
                        // Compressed instruction completely satisfied by skid buffer
  assign output_valid = skid_complete_instr |
                        // Output data available and, output stream aligned, or skid data available,
                        (data_valid & (~output_addr_q[1] | skid_valid_q |
                                       // or this is an error or an unaligned compressed instruction
                                       output_err | (output_data[17:16] != 2'b11)));

  // Update the address on branches and every time an instruction is driven
  assign output_addr_en = branch_or_mispredict | (ready_i & valid_o);

  // Increment the address by two every time a compressed instruction is popped
  assign addr_incr_two = output_compressed & ~err_o;

  // Next IF stage PC
  assign output_addr_incr = (output_addr_q[31:1] +
                             // Increment address by 4 or 2
                             {29'd0, ~addr_incr_two, addr_incr_two});

  // Redirect the address on branches or mispredicts
  assign output_addr_d = branch_i            ? addr_i[31:1] :
                         branch_mispredict_i ? branch_mispredict_addr[31:1] :
                                               output_addr_incr;

  always_ff @(posedge clk_i) begin
    if (output_addr_en) begin
      output_addr_q <= output_addr_d;
    end
  end

  // Mux the data from BusWidth to halfword
  // This muxing realigns data when instruction words are split across BUS_W e.g.
  // word 1 |----|*h1*|
  // word 0 |*h0*|----| --> |*h1*|*h0*|
  //        31   15   0     31   15   0
  always_comb begin
    output_data_lo = '0;
    for (int i = 0; i < OUTPUT_BEATS; i++) begin
      if (output_addr_q[BUS_W-1:1] == i[BUS_W-2:0]) begin
        output_data_lo |= output_data[i*16+:16];
      end
    end
  end

  always_comb begin
    output_data_hi = '0;
    for (int i = 0; i < OUTPUT_BEATS-1; i++) begin
      if (output_addr_q[BUS_W-1:1] == i[BUS_W-2:0]) begin
        output_data_hi |= output_data[(i+1)*16+:16];
      end
    end
    if (&output_addr_q[BUS_W-1:1]) begin
      output_data_hi |= output_data[15:0];
    end
  end

  assign valid_o     = output_valid & ~branch_mispredict_i;
  assign rdata_o     = {output_data_hi, (skid_valid_q ? skid_data_q : output_data_lo)};
  assign addr_o      = {output_addr_q, 1'b0};
  assign err_o       = (skid_valid_q & skid_err_q) | (~skid_complete_instr & output_err);
  // Error caused by the second half of a misaligned uncompressed instruction
  // (only relevant when err_o is set)
  assign err_plus2_o = skid_valid_q & ~skid_err_q;

  ///////////////////
  // Invalidations //
  ///////////////////

  // Invalidate on reset, or when instructed. If an invalidation request is received while a
  // previous invalidation is ongoing, it does not need to be restarted.
  assign start_inval   = (~reset_inval_q | icache_inval_i) & ~inval_prog_q;
  assign inval_prog_d  = start_inval | (inval_prog_q & ~inval_done);
  assign inval_done    = &inval_index_q;
  assign inval_index_d = start_inval ? '0 :
                                       (inval_index_q + {{INDEX_W-1{1'b0}},1'b1});

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      inval_prog_q  <= 1'b0;
      reset_inval_q <= 1'b0;
    end else begin
      inval_prog_q  <= inval_prog_d;
      reset_inval_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i) begin
    if (inval_prog_d) begin
      inval_index_q <= inval_index_d;
    end
  end

  /////////////////
  // Busy status //
  /////////////////

  // Only busy (for WFI purposes) while an invalidation is in-progress, or external requests are
  // outstanding.
  assign busy_o = inval_prog_q | (|(fill_busy_q & ~fill_rvd_done));

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_INIT(size_param_legal, (LineSize > 32))

  // ECC primitives will need to be changed for different sizes
  `ASSERT_INIT(ecc_tag_param_legal, (TAG_SIZE <= 27))
  `ASSERT_INIT(ecc_data_param_legal, (LineSize <= 121))

  // Lookups in the tag ram should always give a known result
  `ASSERT_KNOWN(TagHitKnown,     lookup_valid_ic1 & tag_hit_ic1)
  `ASSERT_KNOWN(TagInvalidKnown, lookup_valid_ic1 & tag_invalid_ic1)

  // This is only used for the Yosys-based formal flow. Once we have working bind support, we can
  // get rid of it.
`ifdef FORMAL
 `ifdef YOSYS
  // Unfortunately, Yosys doesn't support passing unpacked arrays as ports. Explicitly pack up the
  // signals we need.
  logic [NUM_FB-1:0][ADDR_W-1:0] packed_fill_addr_q;
  always_comb begin
    for (int i = 0; i < NUM_FB; i++) begin
      packed_fill_addr_q[i][ADDR_W-1:0] = fill_addr_q[i];
    end
  end

  `include "formal_tb_frag.svh"
 `endif
`endif


endmodule
