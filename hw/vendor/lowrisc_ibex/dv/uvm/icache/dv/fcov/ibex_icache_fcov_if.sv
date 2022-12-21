interface ibex_icache_fcov_if import ibex_pkg::*; #(
  parameter int NUM_FB = 4
) (
  input                   clk_i,
  input                   rst_ni,
  input                   req_i,
  input                   branch_i,
  input                   icache_enable_i,
  input                   icache_inval_i,
  input                   lookup_throttle,
  input                   lookup_req_ic0,
  input                   tag_req_ic0,
  input                   data_req_ic0,
  input                   fill_req_ic0,
  input                   inval_write_req,
  input                   ecc_write_req,
  input                   skid_valid_q,
  input                   valid_o,
  input [ADDR_W-1:0]      lookup_addr_ic0,
  input                   lookup_valid_ic1,
  input                   tag_hit_ic1,
  input [IC_NUM_WAYS-1:0] tag_match_ic1,

  input [NUM_FB-1:0]                    fill_hit_ic1,
  input [NUM_FB-1:0]                    fill_busy_q,
  input [NUM_FB-1:0]                    fill_rvd_done,
  input [NUM_FB-1:0]                    fill_ram_done_q,
  input [NUM_FB-1:0]                    fill_hit_q,
  input [NUM_FB-1:0]                    fill_cache_q,
  input [NUM_FB-1:0]                    fill_stale_q,
  input [NUM_FB-1:0]                    fill_done,
  input [NUM_FB-1:0]                    fill_ext_hold_q,
  input [NUM_FB-1:0]                    fill_ext_done_q,
  logic [NUM_FB-1:0]                    fill_data_hit,
  logic [NUM_FB-1:0]                    fill_data_rvd,
  logic [NUM_FB-1:0]                    fill_alloc,
  logic [NUM_FB-1:0][NUM_FB-1:0]        fill_older_q,
  input [NUM_FB-1:0][IC_LINE_BEATS-1:0] fill_err_q,
  input [NUM_FB-1:0][IC_LINE_BEATS_W:0] fill_rvd_cnt_q,
  input [NUM_FB-1:0][IC_LINE_BEATS_W:0] fill_ext_cnt_q,
  input [ADDR_W-1:0]                    fill_addr_q [NUM_FB]
);
  localparam int IC_NUM_WAYS_W = $clog2(IC_NUM_WAYS);

  function automatic logic [IC_NUM_WAYS_W-1:0] way_num(logic [IC_NUM_WAYS-1:0] way_onehot);
    for (int i = 0;i < IC_NUM_WAYS; ++i) begin
      if (way_onehot[i]) begin
        return i;
      end
    end

    return 'x;
  endfunction

  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  typedef enum {
    FillBufIdle,
    FillBufReqing,
    FillBufReqingAndFilling,
    FillBufFilling,
    FillBufAllocating,
    FillBufAwaitingOutput
  } fill_buffer_state_e;

  typedef enum {
    FillBufNotDone,
    FillBufDoneHitNoExtReqs,
    FillBufDoneHitExtReqs,
    FillBufDoneMiss,
    FillBufDoneBranchNoExtReqs,
    FillBufDoneBranchExtReqs,
    FillBufDoneNoCache,
    FillBufDoneMemErr
  } fill_buffer_done_reason_e;

  typedef enum {
    ICDataSrcCache,
    ICDataSrcFB,
    ICDataSrcExt
  } ic_data_src_e;

  bit en_icache_fcov = 0;

  initial begin
   void'($value$plusargs("enable_icache_fcov=%d", en_icache_fcov));
  end

  ic_data_src_e ic_data_src;

  always_comb begin
    ic_data_src = ICDataSrcFB;
    if (|fill_data_rvd) begin
      ic_data_src = ICDataSrcExt;
    end else if (|fill_data_hit) begin
      ic_data_src = ICDataSrcCache;
    end
  end

  logic [IC_LINE_BEATS-1:0] data_err_ecc;
  for (genvar i_beat = 0; i_beat < IC_LINE_BEATS; ++i_beat) begin : g_data_err_ecc
    assign data_err_ecc[i_beat] = |gen_data_ecc_checking.data_err_ic1[i_beat*2+:2];
  end

  covergroup icache_cg @(posedge clk_i);
    option.per_instance = 1;
    option.name = "icache_cg";

    `DV_FCOV_EXPR_SEEN(req_when_fb_full, req_i & (&fill_busy_q))
    `DV_FCOV_EXPR_SEEN(branch_when_fb_full, branch_i & (&fill_busy_q))
    `DV_FCOV_EXPR_SEEN(throttle_req, lookup_throttle & lookup_req_ic0)

    cp_lookup_req: coverpoint branch_i iff (lookup_req_ic0) {
      bins straightline_req = {1'b0};
      bins branch_req = {1'b1};
    }

    cp_fill_buffer_usage: coverpoint $countones(fill_busy_q) {
      bins fill_level[] = {[0:NUM_FB]};
      illegal_bins illegal = default;
    }

    cp_hit_miss: coverpoint tag_hit_ic1 iff (lookup_valid_ic1) {
      bins miss = {1'b0};
      bins hit = {1'b1};
    }

    cp_hit_way: coverpoint way_num(tag_match_ic1) iff (lookup_valid_ic1 && tag_hit_ic1);

    cp_data_ecc_err: coverpoint data_err_ecc
      iff (lookup_valid_ic1 && tag_hit_ic1);

    cp_tag_ecc_err: coverpoint way_num(gen_data_ecc_checking.tag_err_ic1) iff (lookup_valid_ic1);

    cp_data_src: coverpoint ic_data_src iff (valid_o);

    tag_req_cross: cross req_i, branch_i, fill_req_ic0, inval_write_req, ecc_write_req {
      // The ICache will still perform lookups when we assert branch_i without req_i but this is not
      // a behaviour Ibex uses
      ignore_bins branch_no_req =
        binsof(req_i) intersect {1'b0} && binsof(branch_i) intersect {1'b1};

      // When we're invalidating fill and ecc requests cannot occur
      illegal_bins illegal_with_inval = binsof(inval_write_req) intersect {1'b1} && (
        binsof(fill_req_ic0) intersect {1'b1} ||
        binsof(ecc_write_req) intersect {1'b1});
    }

    data_req_cross: cross fill_req_ic0, cp_lookup_req iff (data_req_ic0);
    data_src_cross: cross icache_enable_i, skid_valid_q, cp_data_src iff (valid_o);
  endgroup

  `DV_FCOV_INSTANTIATE_CG(icache_cg, en_icache_fcov)

  logic last_icache_enable;
  logic last_icache_inval;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_icache_enable <= 1'b0;
      last_icache_inval  <= 1'b0;
    end else begin
      last_icache_enable <= icache_enable_i;
      last_icache_inval  <= icache_inval_i;
    end
  end

  logic icache_just_disabled, icache_just_enabled;
  logic icache_inval_start;

  assign icache_just_disabled =  last_icache_enable & ~icache_enable_i;
  assign icache_just_enabled  = ~last_icache_enable &  icache_enable_i;

  assign icache_inval_start = ~last_icache_inval & icache_inval_i;

  logic [IC_LINE_BEATS_W-1:0] starting_beat;
  assign starting_beat = lookup_addr_ic0[IC_LINE_W-1:BUS_W];

  for (genvar i_fb = 0;i_fb < NUM_FB; ++i_fb) begin : g_fb_cov
    fill_buffer_state_e fill_buffer_state;
    logic fill_alloc_done_or_skip;
    logic fill_requesting;

    assign fill_alloc_done_or_skip =
      fill_ram_done_q[i_fb] | fill_hit_q[i_fb] | ~fill_cache_q[i_fb] | (|fill_err_q[i_fb]);

    assign fill_requesting = !fill_ext_done_q[i_fb] && (fill_rvd_cnt_q[i_fb] == '0)
              && (fill_ext_cnt_q[i_fb] != IC_LINE_BEATS);

    always_comb begin
      fill_buffer_state = FillBufIdle;

      if (fill_busy_q[i_fb]) begin
        if (fill_requesting) begin
          fill_buffer_state = FillBufReqing;
        end else if (!fill_rvd_done[i_fb]) begin
          if (!fill_ext_done_q[i_fb]) begin
            fill_buffer_state = FillBufReqingAndFilling;
          end else begin
            fill_buffer_state = FillBufFilling;
          end
        end else if (!fill_alloc_done_or_skip) begin
          fill_buffer_state = FillBufAllocating;
        end else begin
          fill_buffer_state = FillBufAwaitingOutput;
        end
      end
    end

    logic fill_awaiting_ext_req;

    fill_buffer_done_reason_e fill_buffer_done_reason;

    assign fill_has_ext_req = (fill_ext_cnt_q[i_fb] != '0) || fill_ext_hold_q[i_fb];

    always_comb begin
      fill_buffer_done_reason = FillBufNotDone;

      if (fill_done[i_fb]) begin
        if (|fill_err_q[i_fb]) begin
          fill_buffer_done_reason = FillBufDoneMemErr;
        end else if (~fill_cache_q[i_fb]) begin
          if (branch_i || fill_stale_q[i_fb]) begin
            fill_buffer_done_reason = fill_has_ext_req ? FillBufDoneBranchExtReqs :
                                                         FillBufDoneBranchNoExtReqs;
          end else begin
            fill_buffer_done_reason = FillBufDoneNoCache;
          end
        end else if (fill_hit_q[i_fb]) begin
          fill_buffer_done_reason = fill_has_ext_req ? FillBufDoneHitExtReqs :
                                                       FillBufDoneHitNoExtReqs;
        end else begin
          fill_buffer_done_reason = FillBufDoneMiss;
        end
      end
    end

    logic [NUM_FB-1:0] addr_matches;

    for (genvar i_other_fb = 0; i_other_fb < NUM_FB; ++i_other_fb) begin : g_other_fb
      if (i_other_fb != i_fb) begin
        assign addr_matches[i_other_fb] = fill_busy_q[i_fb] & fill_busy_q[i_other_fb] &
          (fill_addr_q[i_fb] == fill_addr_q[i_other_fb]);
      end else begin
        assign addr_matches[i_other_fb] = 1'b0;
      end
    end


    covergroup icache_fillbuf_cg @(posedge clk_i);
      option.per_instance = 1;
      option.name = "icache_fillbuf_cg";

      `DV_FCOV_EXPR_SEEN(addr_hz, |addr_matches)

      cp_out_of_order_finish: coverpoint $countones(fill_older_q[i_fb] & fill_busy_q)
        iff (fill_done[i_fb]) {
        bins older_fill_bufs[] = {[0:NUM_FB-1]};
        illegal_bins illegal = default;
      }
      cp_state: coverpoint fill_buffer_state;
      cp_fill_buffer_done_reason : coverpoint fill_buffer_done_reason;
      cp_state_when_disabling: coverpoint fill_buffer_state iff icache_just_disabled;
      cp_state_when_enabling: coverpoint fill_buffer_state iff icache_just_enabled;
      cp_state_when_inval_start: coverpoint fill_buffer_state iff icache_inval_start;
      cp_starting_beat: coverpoint starting_beat iff fill_alloc[i_fb];
    endgroup

    `DV_FCOV_INSTANTIATE_CG(icache_fillbuf_cg, en_icache_fcov)
  end
endinterface
