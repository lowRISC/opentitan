// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src core module
//

module entropy_src_core import entropy_src_pkg::*; #(
  parameter int EsFifoDepth = 4,
  parameter int DistrFifoDepth = 2
) (
  input logic clk_i,
  input logic rst_ni,

  input  entropy_src_reg_pkg::entropy_src_reg2hw_t reg2hw,
  output entropy_src_reg_pkg::entropy_src_hw2reg_t hw2reg,

  // Efuse Interface
  input prim_mubi_pkg::mubi8_t otp_en_entropy_src_fw_read_i,
  input prim_mubi_pkg::mubi8_t otp_en_entropy_src_fw_over_i,

  // RNG Interface
  output logic rng_fips_o,

  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // RNG Interface
  output entropy_src_rng_req_t entropy_src_rng_o,
  input  entropy_src_rng_rsp_t entropy_src_rng_i,

  // CSRNG Interface
  output cs_aes_halt_req_t cs_aes_halt_o,
  input  cs_aes_halt_rsp_t cs_aes_halt_i,

  // External Health Test Interface
  output entropy_src_xht_req_t entropy_src_xht_o,
  input  entropy_src_xht_rsp_t entropy_src_xht_i,

  output logic           recov_alert_test_o,
  output logic           fatal_alert_test_o,
  output logic           recov_alert_o,
  output logic           fatal_alert_o,

  output logic           intr_es_entropy_valid_o,
  output logic           intr_es_health_test_failed_o,
  output logic           intr_es_observe_fifo_ready_o,
  output logic           intr_es_fatal_err_o
);

  import entropy_src_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_and_hi;
  import prim_mubi_pkg::mubi4_test_false_loose;
  import prim_mubi_pkg::mubi4_test_invalid;

  localparam int EsFifoDepthW = prim_util_pkg::vbits(EsFifoDepth);
  localparam int PostHTWidth = 32;
  localparam int RngBusWidth = 4;
  localparam int HalfRegWidth = 16;
  localparam int FullRegWidth = 32;
  localparam int EighthRegWidth = 4;
  localparam int SeedLen = 384;
  localparam int DistrFifoWidth = 32;
  localparam int ObserveFifoWidth = 32;
  localparam int PreCondWidth = 64;
  localparam int Clog2ObserveFifoDepth = $clog2(ObserveFifoDepth);
  localparam int EsEnableCopies = 20;
  localparam int EsEnPulseCopies = 1;
  localparam int unsigned NumSwReadsSeed = SeedLen / FullRegWidth;
  localparam int unsigned LastSwRead = NumSwReadsSeed - 1;
  localparam int unsigned SwReadIdxWidth = prim_util_pkg::vbits(NumSwReadsSeed);

  //-----------------------
  // SHA3parameters
  //-----------------------
  // Do not enable masking
  localparam bit Sha3EnMasking = 0;
  // derived parameter
  localparam int Sha3Share = (Sha3EnMasking) ? 2 : 1;

  // signals
  logic       fw_ov_mode;
  logic       fw_ov_mode_pfe;
  logic       fw_ov_mode_pfa;
  logic       fw_ov_wr_fifo_full;
  logic       fw_ov_mode_entropy_insert;
  logic       fw_ov_entropy_insert_pfe;
  logic       fw_ov_entropy_insert_pfa;
  logic       fw_ov_sha3_start_pfe;
  logic       fw_ov_sha3_start_pfe_q;
  logic       fw_ov_sha3_start_pfa;
  logic       fw_ov_sha3_disable_pulse;
  logic [ObserveFifoWidth-1:0] fw_ov_wr_data;
  logic       fw_ov_fifo_rd_pulse;
  logic       fw_ov_fifo_wr_pulse;
  logic       es_enable_pfa;

  logic       fips_enable_pfe;
  logic       fips_enable_pfa;
  logic       fips_flag_pfe;
  logic       fips_flag_pfa;
  logic       rng_fips_pfe;
  logic       rng_fips_pfa;

  logic       rng_bit_en;
  logic       rng_bit_enable_pfe;
  logic       rng_bit_enable_pfa;
  logic [1:0] rng_bit_sel;
  logic       rng_enable_q, rng_enable_d;
  logic       entropy_data_reg_en_pfe;
  logic       entropy_data_reg_en_pfa;
  logic       es_data_reg_rd_en;
  logic       event_es_entropy_valid;
  logic       event_es_health_test_failed;
  logic       event_es_observe_fifo_ready;
  logic       event_es_fatal_err;
  logic       es_rng_src_valid;
  logic [RngBusWidth-1:0] es_rng_bus;

  logic [RngBusWidth-1:0] sfifo_esrng_wdata;
  logic [RngBusWidth-1:0] sfifo_esrng_rdata;
  logic                   sfifo_esrng_push;
  logic                   sfifo_esrng_pop;
  logic                   sfifo_esrng_clr;
  logic                   sfifo_esrng_full;
  logic                   sfifo_esrng_not_empty;
  logic                   sfifo_esrng_not_full;
  logic                   sfifo_esrng_int_err;
  logic [2:0]             sfifo_esrng_err;

  logic [DistrFifoWidth-1:0] sfifo_distr_wdata;
  logic [DistrFifoWidth-1:0] sfifo_distr_rdata;
  logic                      sfifo_distr_push;
  logic                      sfifo_distr_pop;
  logic                      sfifo_distr_clr;
  logic                      sfifo_distr_not_full;
  logic                      sfifo_distr_full;
  logic                      sfifo_distr_not_empty;
  logic                      sfifo_distr_int_err;
  logic [2:0]                sfifo_distr_err;

  logic [ObserveFifoWidth-1:0]    sfifo_observe_wdata;
  logic [ObserveFifoWidth-1:0]    sfifo_observe_rdata;
  logic                           sfifo_observe_push;
  logic                           sfifo_observe_pop;
  logic                           sfifo_observe_full;
  logic                           sfifo_observe_clr;
  logic                           sfifo_observe_not_empty;
  logic [Clog2ObserveFifoDepth:0] sfifo_observe_depth;
  logic                           sfifo_observe_int_err;
  logic [2:0]                     sfifo_observe_err;

  logic [EsFifoDepthW-1:0]   sfifo_esfinal_depth;
  logic [(1+SeedLen)-1:0]    sfifo_esfinal_wdata;
  logic [(1+SeedLen)-1:0]    sfifo_esfinal_rdata;
  logic                      sfifo_esfinal_push;
  logic                      sfifo_esfinal_pop;
  logic                      sfifo_esfinal_clr;
  logic                      sfifo_esfinal_not_full;
  logic                      sfifo_esfinal_full;
  logic                      sfifo_esfinal_not_empty;
  logic                      sfifo_esfinal_int_err;
  logic [2:0]                sfifo_esfinal_err;

  logic                   es_sfifo_int_err;

  logic [SeedLen-1:0]     esfinal_data;
  logic                   esfinal_fips_flag;

  logic                   any_fail_pulse;
  logic                   main_stage_push;
  logic                   main_stage_push_raw;
  logic                   bypass_stage_pop;
  logic                   boot_phase_done;
  logic [HalfRegWidth-1:0] any_fail_count;
  logic                    any_fails_cntr_err;
  logic                    alert_threshold_fail;
  logic [HalfRegWidth-1:0] alert_threshold;
  logic [HalfRegWidth-1:0] alert_threshold_inv;
  logic [Clog2ObserveFifoDepth:0] observe_fifo_thresh;
  logic                     observe_fifo_thresh_met;
  logic                     repcnt_active;
  logic                     repcnts_active;
  logic                     adaptp_active;
  logic                     bucket_active;
  logic                     markov_active;
  logic                     extht_active;
  logic                     alert_cntrs_clr;
  logic                     health_test_clr;
  logic                     health_test_done_pulse;
  logic [RngBusWidth-1:0]   health_test_esbus;
  logic                     health_test_esbus_vld;
  logic                     es_route_pfe;
  logic                     es_route_pfa;
  logic                     es_type_pfe;
  logic                     es_type_pfa;
  logic                     es_route_to_sw;
  logic                     es_bypass_to_sw;
  logic                     es_bypass_mode;
  logic                     rst_alert_cntr;
  logic                     threshold_scope;
  logic                     threshold_scope_pfe;
  logic                     threshold_scope_pfa;
  logic                     fips_compliance;

  logic [HalfRegWidth-1:0] health_test_fips_window;
  logic [HalfRegWidth-1:0] health_test_bypass_window;
  logic [HalfRegWidth-1:0] health_test_window;
  logic [WINDOW_CNTR_WIDTH-1:0] health_test_window_scaled;

  logic [HalfRegWidth-1:0] repcnt_fips_threshold;
  logic [HalfRegWidth-1:0] repcnt_fips_threshold_oneway;
  logic                    repcnt_fips_threshold_wr;
  logic [HalfRegWidth-1:0] repcnt_bypass_threshold;
  logic [HalfRegWidth-1:0] repcnt_bypass_threshold_oneway;
  logic                    repcnt_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] repcnt_threshold;
  logic [HalfRegWidth-1:0] repcnt_event_cnt;
  logic [HalfRegWidth-1:0] repcnt_event_hwm_fips;
  logic [HalfRegWidth-1:0] repcnt_event_hwm_bypass;
  logic [FullRegWidth-1:0] repcnt_total_fails;
  logic [EighthRegWidth-1:0] repcnt_fail_count;
  logic                     repcnt_fail_pulse;
  logic                     repcnt_fails_cntr_err;
  logic                     repcnt_alert_cntr_err;

  logic [HalfRegWidth-1:0] repcnts_fips_threshold;
  logic [HalfRegWidth-1:0] repcnts_fips_threshold_oneway;
  logic                    repcnts_fips_threshold_wr;
  logic [HalfRegWidth-1:0] repcnts_bypass_threshold;
  logic [HalfRegWidth-1:0] repcnts_bypass_threshold_oneway;
  logic                    repcnts_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] repcnts_threshold;
  logic [HalfRegWidth-1:0] repcnts_event_cnt;
  logic [HalfRegWidth-1:0] repcnts_event_hwm_fips;
  logic [HalfRegWidth-1:0] repcnts_event_hwm_bypass;
  logic [FullRegWidth-1:0] repcnts_total_fails;
  logic [EighthRegWidth-1:0] repcnts_fail_count;
  logic                     repcnts_fail_pulse;
  logic                     repcnts_fails_cntr_err;
  logic                     repcnts_alert_cntr_err;

  logic [HalfRegWidth-1:0] adaptp_hi_fips_threshold;
  logic [HalfRegWidth-1:0] adaptp_hi_fips_threshold_oneway;
  logic                    adaptp_hi_fips_threshold_wr;
  logic [HalfRegWidth-1:0] adaptp_hi_bypass_threshold;
  logic [HalfRegWidth-1:0] adaptp_hi_bypass_threshold_oneway;
  logic                    adaptp_hi_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] adaptp_hi_threshold;
  logic [HalfRegWidth-1:0] adaptp_lo_fips_threshold;
  logic [HalfRegWidth-1:0] adaptp_lo_fips_threshold_oneway;
  logic                    adaptp_lo_fips_threshold_wr;
  logic [HalfRegWidth-1:0] adaptp_lo_bypass_threshold;
  logic [HalfRegWidth-1:0] adaptp_lo_bypass_threshold_oneway;
  logic                    adaptp_lo_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] adaptp_lo_threshold;
  logic [HalfRegWidth-1:0] adaptp_hi_event_cnt;
  logic [HalfRegWidth-1:0] adaptp_lo_event_cnt;
  logic [HalfRegWidth-1:0] adaptp_hi_event_hwm_fips;
  logic [HalfRegWidth-1:0] adaptp_hi_event_hwm_bypass;
  logic [HalfRegWidth-1:0] adaptp_lo_event_hwm_fips;
  logic [HalfRegWidth-1:0] adaptp_lo_event_hwm_bypass;
  logic [FullRegWidth-1:0] adaptp_hi_total_fails;
  logic [FullRegWidth-1:0] adaptp_lo_total_fails;
  logic [EighthRegWidth-1:0] adaptp_hi_fail_count;
  logic [EighthRegWidth-1:0] adaptp_lo_fail_count;
  logic                     adaptp_hi_fail_pulse;
  logic                     adaptp_lo_fail_pulse;
  logic                     adaptp_hi_fails_cntr_err;
  logic                     adaptp_lo_fails_cntr_err;
  logic                     adaptp_hi_alert_cntr_err;
  logic                     adaptp_lo_alert_cntr_err;

  logic [HalfRegWidth-1:0] bucket_fips_threshold;
  logic [HalfRegWidth-1:0] bucket_fips_threshold_oneway;
  logic                    bucket_fips_threshold_wr;
  logic [HalfRegWidth-1:0] bucket_bypass_threshold;
  logic [HalfRegWidth-1:0] bucket_bypass_threshold_oneway;
  logic                    bucket_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] bucket_threshold;
  logic [HalfRegWidth-1:0] bucket_event_cnt;
  logic [HalfRegWidth-1:0] bucket_event_hwm_fips;
  logic [HalfRegWidth-1:0] bucket_event_hwm_bypass;
  logic [FullRegWidth-1:0] bucket_total_fails;
  logic [EighthRegWidth-1:0] bucket_fail_count;
  logic                     bucket_fail_pulse;
  logic                     bucket_fails_cntr_err;
  logic                     bucket_alert_cntr_err;

  logic [HalfRegWidth-1:0] markov_hi_fips_threshold;
  logic [HalfRegWidth-1:0] markov_hi_fips_threshold_oneway;
  logic                    markov_hi_fips_threshold_wr;
  logic [HalfRegWidth-1:0] markov_hi_bypass_threshold;
  logic [HalfRegWidth-1:0] markov_hi_bypass_threshold_oneway;
  logic                    markov_hi_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] markov_hi_threshold;
  logic [HalfRegWidth-1:0] markov_lo_fips_threshold;
  logic [HalfRegWidth-1:0] markov_lo_fips_threshold_oneway;
  logic                    markov_lo_fips_threshold_wr;
  logic [HalfRegWidth-1:0] markov_lo_bypass_threshold;
  logic [HalfRegWidth-1:0] markov_lo_bypass_threshold_oneway;
  logic                    markov_lo_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] markov_lo_threshold;
  logic [HalfRegWidth-1:0] markov_hi_event_cnt;
  logic [HalfRegWidth-1:0] markov_lo_event_cnt;
  logic [HalfRegWidth-1:0] markov_hi_event_hwm_fips;
  logic [HalfRegWidth-1:0] markov_hi_event_hwm_bypass;
  logic [HalfRegWidth-1:0] markov_lo_event_hwm_fips;
  logic [HalfRegWidth-1:0] markov_lo_event_hwm_bypass;
  logic [FullRegWidth-1:0] markov_hi_total_fails;
  logic [FullRegWidth-1:0] markov_lo_total_fails;
  logic [EighthRegWidth-1:0] markov_hi_fail_count;
  logic [EighthRegWidth-1:0] markov_lo_fail_count;
  logic                     markov_hi_fail_pulse;
  logic                     markov_lo_fail_pulse;
  logic                     markov_hi_fails_cntr_err;
  logic                     markov_lo_fails_cntr_err;
  logic                     markov_hi_alert_cntr_err;
  logic                     markov_lo_alert_cntr_err;

  logic [HalfRegWidth-1:0] extht_hi_fips_threshold;
  logic [HalfRegWidth-1:0] extht_hi_fips_threshold_oneway;
  logic                    extht_hi_fips_threshold_wr;
  logic [HalfRegWidth-1:0] extht_hi_bypass_threshold;
  logic [HalfRegWidth-1:0] extht_hi_bypass_threshold_oneway;
  logic                    extht_hi_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] extht_hi_threshold;
  logic [HalfRegWidth-1:0] extht_lo_fips_threshold;
  logic [HalfRegWidth-1:0] extht_lo_fips_threshold_oneway;
  logic                    extht_lo_fips_threshold_wr;
  logic [HalfRegWidth-1:0] extht_lo_bypass_threshold;
  logic [HalfRegWidth-1:0] extht_lo_bypass_threshold_oneway;
  logic                    extht_lo_bypass_threshold_wr;
  logic [HalfRegWidth-1:0] extht_lo_threshold;
  logic [HalfRegWidth-1:0] extht_event_cnt_hi;
  logic [HalfRegWidth-1:0] extht_event_cnt_lo;
  logic [HalfRegWidth-1:0] extht_hi_event_hwm_fips;
  logic [HalfRegWidth-1:0] extht_hi_event_hwm_bypass;
  logic [HalfRegWidth-1:0] extht_lo_event_hwm_fips;
  logic [HalfRegWidth-1:0] extht_lo_event_hwm_bypass;
  logic [FullRegWidth-1:0] extht_hi_total_fails;
  logic [FullRegWidth-1:0] extht_lo_total_fails;
  logic [EighthRegWidth-1:0] extht_hi_fail_count;
  logic [EighthRegWidth-1:0] extht_lo_fail_count;
  logic                     extht_hi_fail_pulse;
  logic                     extht_lo_fail_pulse;
  logic                     extht_cont_test;
  logic                     extht_hi_fails_cntr_err;
  logic                     extht_lo_fails_cntr_err;
  logic                     extht_hi_alert_cntr_err;
  logic                     extht_lo_alert_cntr_err;


  logic                     pfifo_esbit_wdata;
  logic [RngBusWidth-1:0]   pfifo_esbit_rdata;
  logic                     pfifo_esbit_not_empty;
  logic                     pfifo_esbit_not_full;
  logic                     pfifo_esbit_push;
  logic                     pfifo_esbit_clr;
  logic                     pfifo_esbit_pop;

  logic [RngBusWidth-1:0]   pfifo_postht_wdata;
  logic [PostHTWidth-1:0]   pfifo_postht_rdata;
  logic                     pfifo_postht_not_empty;
  logic                     pfifo_postht_not_full;
  logic                     pfifo_postht_push;
  logic                     pfifo_postht_clr;
  logic                     pfifo_postht_pop;

  logic [PreCondWidth-1:0]  pfifo_cond_wdata;
  logic [SeedLen-1:0]       pfifo_cond_rdata;
  logic                     pfifo_cond_push;

  logic [ObserveFifoWidth-1:0] pfifo_precon_wdata;
  logic [PreCondWidth-1:0]     pfifo_precon_rdata;
  logic                        pfifo_precon_not_empty;
  logic                        pfifo_precon_not_full;
  logic                        pfifo_precon_push;
  logic                        pfifo_precon_clr;
  logic                        pfifo_precon_pop;

  logic [PostHTWidth-1:0]   pfifo_bypass_wdata;
  logic [SeedLen-1:0]       pfifo_bypass_rdata;
  logic                     pfifo_bypass_not_empty;
  logic                     pfifo_bypass_not_full;
  logic                     pfifo_bypass_push;
  logic                     pfifo_bypass_clr;
  logic                     pfifo_bypass_pop;

  logic [SwReadIdxWidth-1:0] swread_idx_d, swread_idx_q;
  logic                      swread_idx_incr, swread_idx_clr;
  logic [FullRegWidth-1:0]   swread_data, swread_data_buf;
  logic                      swread_done;

  logic [SeedLen-1:0]       final_es_data;
  logic                     es_hw_if_req;
  logic                     es_hw_if_ack;
  logic                     es_hw_if_fifo_pop;
  logic                     sfifo_esrng_err_sum;
  logic                     sfifo_distr_err_sum;
  logic                     sfifo_observe_err_sum;
  logic                     sfifo_esfinal_err_sum;
  // For fifo errors that are generated through the
  // ERR_CODE_TEST register, but are not associated
  // with any errors:
  logic                         sfifo_test_err_sum;
  logic                         es_ack_sm_err_sum;
  logic                         es_ack_sm_err;
  logic                         es_main_sm_err_sum;
  logic                         es_main_sm_err;
  logic                         es_main_sm_alert;
  logic                         es_bus_cmp_alert;
  logic                         es_thresh_cfg_alert;
  logic                         es_main_sm_idle;
  logic [8:0]                   es_main_sm_state;
  logic                         fifo_write_err_sum;
  logic                         fifo_read_err_sum;
  logic                         fifo_status_err_sum;
  logic [30:0]                  err_code_test_bit;
  logic                         sha3_msgfifo_ready;
  logic                         sha3_state_vld;
  logic                         sha3_start_raw;
  logic                         sha3_start;
  logic                         sha3_process;
  logic                         sha3_block_processed;
  prim_mubi_pkg::mubi4_t        sha3_done;
  prim_mubi_pkg::mubi4_t        sha3_absorbed;
  logic                         sha3_squeezing;
  logic [2:0]                   sha3_fsm;
  logic [32:0]                  sha3_err;
  logic                         cs_aes_halt_req;
  logic [WINDOW_CNTR_WIDTH-1:0] window_cntr;
  logic                         window_cntr_incr_en;

  logic [sha3_pkg::StateW-1:0] sha3_state[Sha3Share];
  logic [PreCondWidth-1:0] msg_data[Sha3Share];
  logic                    es_rdata_capt_vld;
  logic                    window_cntr_err;
  logic                    repcnt_cntr_err;
  logic                    repcnts_cntr_err;
  logic                    adaptp_cntr_err;
  logic                    bucket_cntr_err;
  logic                    markov_cntr_err;
  logic                    es_cntr_err;
  logic                    es_cntr_err_sum;
  logic                    sha3_state_error_sum;
  logic                    sha3_rst_storage_err_sum;
  logic                    efuse_es_sw_reg_en;
  logic                    efuse_es_sw_ov_en;

  logic                    sha3_state_error;
  logic                    sha3_count_error;
  logic                    sha3_rst_storage_err;
  logic                    es_hw_regwen;
  logic                    recov_alert_state;
  logic                    es_fw_ov_wr_alert;
  logic                    es_fw_ov_disable_alert;
  logic                    fw_ov_corrupted;
  logic                    postht_entropy_drop_alert;

  logic                    stale_seed_processing;
  logic                    main_sm_enable;
  logic                    main_sm_done_pulse;
  logic                    main_sm_ht_failed;

  logic                    unused_err_code_test_bit;
  logic                    unused_sha3_state;
  logic                    unused_entropy_data;
  logic                    unused_fw_ov_rd_data;
  logic                    unused_sfifo_esrng_not_full;
  logic                    unused_sfifo_esfinal_not_full;

  prim_mubi_pkg::mubi8_t en_entropy_src_fw_read;
  prim_mubi_pkg::mubi8_t en_entropy_src_fw_over;

  mubi4_t mubi_es_enable;
  mubi4_t mubi_module_en_pulse;

  mubi4_t       mubi_module_en_raw;
  mubi4_t [2:0] mubi_module_en_raw_fanout;

  mubi4_t [EsEnableCopies-1:0] mubi_es_enable_fanout;
  logic   [EsEnableCopies-1:0] es_enable_fo;

  mubi4_t [EsEnPulseCopies-1:0] mubi_module_en_pulse_fanout;
  logic   [EsEnPulseCopies-1:0] module_en_pulse_fo;

  // A delayed copy of the enable signal, and enable pulse which are needed to cleanly handle any
  // long-duration operations from the previous run.
  logic                        es_delayed_enable;

  mubi4_t [1:0] mubi_rng_bit_en_fanout;
  mubi4_t mubi_rng_bit_en;

  // flops
  logic        ht_failed_qq, ht_failed_q, ht_failed_d;
  logic        ht_done_pulse_qq, ht_done_pulse_q, ht_done_pulse_d;
  logic        sha3_err_q, sha3_err_d;
  logic        cs_aes_halt_q, cs_aes_halt_d;
  logic [63:0] es_rdata_capt_q, es_rdata_capt_d;
  logic        es_rdata_capt_vld_q, es_rdata_capt_vld_d;
  mubi4_t      mubi_mod_en_dly_d, mubi_mod_en_dly_q;


  logic        sha3_start_mask_q, sha3_start_mask_d;
  logic        sha3_flush_q, sha3_flush_d;
  logic [1:0]  fw_ov_corrupted_q, fw_ov_corrupted_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ht_failed_q            <= '0;
      ht_failed_qq           <= '0;
      ht_done_pulse_q        <= '0;
      ht_done_pulse_qq       <= '0;
      sha3_err_q             <= '0;
      cs_aes_halt_q          <= '0;
      es_rdata_capt_q        <= '0;
      es_rdata_capt_vld_q    <= '0;
      fw_ov_sha3_start_pfe_q <= '0;
      mubi_mod_en_dly_q      <= prim_mubi_pkg::MuBi4False;
      sha3_flush_q           <= '0;
      sha3_start_mask_q      <= '0;
      fw_ov_corrupted_q      <= 2'b00;
      rng_enable_q           <= 1'b 0;
    end else begin
      ht_failed_q            <= ht_failed_d;
      ht_failed_qq           <= ht_failed_q;
      ht_done_pulse_q        <= ht_done_pulse_d;
      ht_done_pulse_qq       <= ht_done_pulse_q;
      sha3_err_q             <= sha3_err_d;
      cs_aes_halt_q          <= cs_aes_halt_d;
      es_rdata_capt_q        <= es_rdata_capt_d;
      es_rdata_capt_vld_q    <= es_rdata_capt_vld_d;
      fw_ov_sha3_start_pfe_q <= fw_ov_sha3_start_pfe;
      sha3_flush_q           <= sha3_flush_d;
      sha3_start_mask_q      <= sha3_start_mask_d;
      mubi_mod_en_dly_q      <= mubi_mod_en_dly_d;
      fw_ov_corrupted_q      <= fw_ov_corrupted_d;
      rng_enable_q           <= rng_enable_d;
    end
  end

  assign fw_ov_sha3_disable_pulse = fw_ov_sha3_start_pfe_q & ~fw_ov_sha3_start_pfe;

  //--------------------------------------------
  // register lock gating
  //--------------------------------------------

  // Allow writes only if
  // 1. SW_REGUPD is true,
  // 2. The DUT is disabled
  //   Block writes if enabled or if internal activities are still in progress (as indicated by
  //   es_delayed_enable).
  assign es_hw_regwen = reg2hw.sw_regupd.q &&
                        mubi4_test_false_loose(mubi_module_en_raw_fanout[0]) &&
                        !es_delayed_enable;
  assign hw2reg.regwen.de = 1'b1;
  assign hw2reg.regwen.d = es_hw_regwen;

  //--------------------------------------------
  // set up secure enable bits
  //--------------------------------------------

  // check for illegal enable field states, and set alert if detected

  // SEC_CM: CONFIG.MUBI
  assign mubi_module_en_raw = mubi4_t'(reg2hw.module_enable.q);
  assign es_enable_pfa      = mubi4_test_invalid(mubi_module_en_raw_fanout[1]);
  assign hw2reg.recov_alert_sts.module_enable_field_alert.de = es_enable_pfa;
  assign hw2reg.recov_alert_sts.module_enable_field_alert.d  = es_enable_pfa;

  prim_mubi4_sync #(
    .NumCopies(3),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_entropy_module_en (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_module_en_raw),
    .mubi_o(mubi_module_en_raw_fanout)
  );

  // Generation of enable pulse, and main enable signals.
  //
  // This module creates a single mubi_encoded module_enable_pulse, as well as
  // a general mubi_es_enable signal.
  //
  // The module enable pulse is MuBi4True for a single clock after the
  // module_enable register is asserted MuBi4True. However in this first clock cycle
  // most of the module is not enabled.  (The enable pulse is for clearing the
  // residual internal state.)
  //
  // The rest of the module is enabled in the second clock cycle after seting the
  // module_enable register to MuBi4True.
  //
  // When module_enable is set to MuBi4False the module is disabled.  No further
  // RNG input is accepted and the state machines transition to Idle as soon as
  // possible. Some delay may occur if the SHA3 conditioning block is busy, though
  // otherwise the main_sm transitions to Idle without delay.

  assign mubi_mod_en_dly_d = mubi_module_en_raw_fanout[2];
  assign mubi_module_en_pulse = mubi4_and_hi(mubi_mod_en_dly_d, mubi4_t'(~mubi_mod_en_dly_q));
  assign mubi_es_enable = mubi4_and_hi(mubi_mod_en_dly_d, mubi_mod_en_dly_q);

  for (genvar i = 0; i < EsEnableCopies; i = i+1) begin : gen_mubi_en_copies
    assign es_enable_fo[i] = mubi4_test_true_strict(mubi_es_enable_fanout[i]);
  end : gen_mubi_en_copies

  prim_mubi4_sync #(
    .NumCopies(EsEnableCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_es_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_es_enable),
    .mubi_o(mubi_es_enable_fanout)
  );

  for (genvar i = 0; i < EsEnPulseCopies; i = i+1) begin : gen_mubi_en_pulse_copies
    assign module_en_pulse_fo[i] = mubi4_test_true_strict(mubi_module_en_pulse_fanout[i]);
  end : gen_mubi_en_pulse_copies

  prim_mubi4_sync #(
    .NumCopies(EsEnPulseCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_es_enable_pulse (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_module_en_pulse),
    .mubi_o(mubi_module_en_pulse_fanout)
  );

  entropy_src_enable_delay u_enable_delay (
    .clk_i,
    .rst_ni,
    .enable_i(es_enable_fo[0]),
    .esrng_fifo_not_empty_i(sfifo_esrng_not_empty),
    .esbit_fifo_not_empty_i(pfifo_esbit_not_empty),
    .postht_fifo_not_empty_i(pfifo_postht_not_empty),
    .distr_fifo_not_empty_i(sfifo_distr_not_empty),
    .cs_aes_halt_req_i(cs_aes_halt_req),
    .sha3_block_processed_i(sha3_block_processed),
    .bypass_mode_i(es_bypass_mode),
    .enable_o(es_delayed_enable)
  );

  mubi4_t mubi_fips_en;
  mubi4_t [1:0] mubi_fips_en_fanout;
  assign mubi_fips_en  = mubi4_t'(reg2hw.conf.fips_enable.q);
  assign fips_enable_pfe = mubi4_test_true_strict(mubi_fips_en_fanout[0]);
  assign fips_enable_pfa = mubi4_test_invalid(mubi_fips_en_fanout[1]);
  assign hw2reg.recov_alert_sts.fips_enable_field_alert.de = fips_enable_pfa;
  assign hw2reg.recov_alert_sts.fips_enable_field_alert.d  = fips_enable_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_entropy_fips_en (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fips_en),
    .mubi_o(mubi_fips_en_fanout)
  );

  mubi4_t mubi_fips_flag;
  mubi4_t [1:0] mubi_fips_flag_fanout;
  assign mubi_fips_flag  = mubi4_t'(reg2hw.conf.fips_flag.q);
  assign fips_flag_pfa = mubi4_test_invalid(mubi_fips_flag_fanout[1]);
  assign fips_flag_pfe = mubi4_test_true_strict(mubi_fips_flag_fanout[0]);
  assign hw2reg.recov_alert_sts.fips_flag_field_alert.de = fips_flag_pfa;
  assign hw2reg.recov_alert_sts.fips_flag_field_alert.d  = fips_flag_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_entropy_fips_flag (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fips_flag),
    .mubi_o(mubi_fips_flag_fanout)
  );

  mubi4_t mubi_rng_fips;
  mubi4_t [1:0] mubi_rng_fips_fanout;
  assign mubi_rng_fips  = mubi4_t'(reg2hw.conf.rng_fips.q);
  assign rng_fips_pfa = mubi4_test_invalid(mubi_rng_fips_fanout[1]);
  assign rng_fips_pfe = prim_mubi_pkg::mubi4_test_true_loose(mubi_rng_fips_fanout[0]);
  assign hw2reg.recov_alert_sts.rng_fips_field_alert.de = rng_fips_pfa;
  assign hw2reg.recov_alert_sts.rng_fips_field_alert.d  = rng_fips_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_entropy_rng_fips (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_rng_fips),
    .mubi_o(mubi_rng_fips_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_entropy_reg_en;
  mubi4_t [1:0] mubi_entropy_reg_en_fanout;
  assign mubi_entropy_reg_en = mubi4_t'(reg2hw.conf.entropy_data_reg_enable.q);
  assign entropy_data_reg_en_pfe = mubi4_test_true_strict(mubi_entropy_reg_en_fanout[0]);
  assign entropy_data_reg_en_pfa = mubi4_test_invalid(mubi_entropy_reg_en_fanout[1]);
  assign hw2reg.recov_alert_sts.entropy_data_reg_en_field_alert.de = entropy_data_reg_en_pfa;
  assign hw2reg.recov_alert_sts.entropy_data_reg_en_field_alert.d =  entropy_data_reg_en_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_entropy_data_reg_en (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_entropy_reg_en),
    .mubi_o(mubi_entropy_reg_en_fanout)
  );

  assign observe_fifo_thresh = reg2hw.observe_fifo_thresh.q;

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_fw_ov_mode;
  mubi4_t [1:0] mubi_fw_ov_mode_fanout;
  assign mubi_fw_ov_mode = mubi4_t'(reg2hw.fw_ov_control.fw_ov_mode.q);
  assign fw_ov_mode_pfe = mubi4_test_true_strict(mubi_fw_ov_mode_fanout[0]);
  assign fw_ov_mode_pfa = mubi4_test_invalid(mubi_fw_ov_mode_fanout[1]);
  assign hw2reg.recov_alert_sts.fw_ov_mode_field_alert.de = fw_ov_mode_pfa;
  assign hw2reg.recov_alert_sts.fw_ov_mode_field_alert.d  = fw_ov_mode_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_fw_ov_mode (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fw_ov_mode),
    .mubi_o(mubi_fw_ov_mode_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_fw_ov_entropy_insert;
  mubi4_t [1:0] mubi_fw_ov_entropy_insert_fanout;
  assign mubi_fw_ov_entropy_insert = mubi4_t'(reg2hw.fw_ov_control.fw_ov_entropy_insert.q);
  assign fw_ov_entropy_insert_pfe = mubi4_test_true_strict(mubi_fw_ov_entropy_insert_fanout[0]);
  assign fw_ov_entropy_insert_pfa = mubi4_test_invalid(mubi_fw_ov_entropy_insert_fanout[1]);
  assign hw2reg.recov_alert_sts.fw_ov_entropy_insert_field_alert.de = fw_ov_entropy_insert_pfa;
  assign hw2reg.recov_alert_sts.fw_ov_entropy_insert_field_alert.d  = fw_ov_entropy_insert_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_fw_ov_entropy_insert (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fw_ov_entropy_insert),
    .mubi_o(mubi_fw_ov_entropy_insert_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_fw_ov_sha3_start;
  mubi4_t [1:0] mubi_fw_ov_sha3_start_fanout;
  assign mubi_fw_ov_sha3_start = mubi4_t'(reg2hw.fw_ov_sha3_start.q);
  assign fw_ov_sha3_start_pfe = mubi4_test_true_strict(mubi_fw_ov_sha3_start_fanout[0]);
  assign fw_ov_sha3_start_pfa = mubi4_test_invalid(mubi_fw_ov_sha3_start_fanout[1]);
  assign hw2reg.recov_alert_sts.fw_ov_sha3_start_field_alert.de = fw_ov_sha3_start_pfa;
  assign hw2reg.recov_alert_sts.fw_ov_sha3_start_field_alert.d  = fw_ov_sha3_start_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_fw_ov_sha3_start (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_fw_ov_sha3_start),
    .mubi_o(mubi_fw_ov_sha3_start_fanout)
  );

  // firmware override controls
  assign fw_ov_mode = efuse_es_sw_ov_en && fw_ov_mode_pfe;
  assign fw_ov_mode_entropy_insert = fw_ov_mode && fw_ov_entropy_insert_pfe;
  assign fw_ov_fifo_rd_pulse = reg2hw.fw_ov_rd_data.re;
  assign hw2reg.fw_ov_rd_data.d = sfifo_observe_rdata;
  assign fw_ov_fifo_wr_pulse = reg2hw.fw_ov_wr_data.qe;
  assign fw_ov_wr_data = reg2hw.fw_ov_wr_data.q;

  assign efuse_es_sw_ov_en = prim_mubi_pkg::mubi8_test_true_strict(en_entropy_src_fw_over);

  prim_mubi8_sync #(
    .NumCopies(1),
    .AsyncOn(1) // must be set to one, see note below
  ) u_prim_mubi8_sync_es_fw_over (
    .clk_i,
    .rst_ni,
    .mubi_i(otp_en_entropy_src_fw_over_i),
    .mubi_o({en_entropy_src_fw_over})
  );

  // note: the input to the above sync module is from the OTP block.
  //       It is assumed that the source is in a different time domain,
  //       and requires the AsyncOn parameter to be set.

  // rng_enable is being used in other clock domains. Need to latch the
  // signal.
  assign rng_enable_d = es_enable_fo[1] &&
                        es_delayed_enable;

  assign entropy_src_rng_o.rng_enable = rng_enable_q;

  assign es_rng_src_valid = entropy_src_rng_i.rng_valid;
  assign es_rng_bus = entropy_src_rng_i.rng_b;


  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_es_entropy_valid (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_es_entropy_valid),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_entropy_valid.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_entropy_valid.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_entropy_valid.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_entropy_valid.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_entropy_valid.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_entropy_valid.d),
    .intr_o                 (intr_es_entropy_valid_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_es_health_test_failed (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_es_health_test_failed),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_health_test_failed.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_health_test_failed.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_health_test_failed.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_health_test_failed.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_health_test_failed.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_health_test_failed.d),
    .intr_o                 (intr_es_health_test_failed_o)
  );


  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_es_observe_fifo_ready (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_es_observe_fifo_ready),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_observe_fifo_ready.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_observe_fifo_ready.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_observe_fifo_ready.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_observe_fifo_ready.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_observe_fifo_ready.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_observe_fifo_ready.d),
    .intr_o                 (intr_es_observe_fifo_ready_o)
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_es_fatal_err (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_es_fatal_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.es_fatal_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.es_fatal_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.es_fatal_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.es_fatal_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.es_fatal_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.es_fatal_err.d),
    .intr_o                 (intr_es_fatal_err_o)
  );

  //--------------------------------------------
  // tlul register settings
  //--------------------------------------------


  // set the interrupt event when enabled
  assign event_es_entropy_valid =
      sfifo_esfinal_not_empty && es_route_to_sw && es_data_reg_rd_en && es_enable_fo[2];


  // Collect all internal FIFO errors.
  assign es_sfifo_int_err = sfifo_esrng_int_err ||
                            sfifo_distr_int_err ||
                            sfifo_observe_int_err ||
                            sfifo_esfinal_int_err;

  // Counter, internal FIFO errors and FSM errors are structural errors and are always active
  // regardless of the functional state.
  logic fatal_loc_events;
  assign fatal_loc_events = es_cntr_err_sum ||
                            es_sfifo_int_err ||
                            es_main_sm_err_sum ||
                            es_ack_sm_err_sum ||
                            sha3_state_error_sum;

  // set the interrupt sources
  assign event_es_fatal_err = (es_enable_fo[3] &&
                                 (sfifo_esrng_err_sum   ||
                                  sfifo_distr_err_sum   ||
                                  sfifo_observe_err_sum ||
                                  sfifo_esfinal_err_sum ||
                                  sfifo_test_err_sum) ) ||
                              sha3_rst_storage_err_sum ||
                              fatal_loc_events;

  // set fifo errors that are single instances of source
  assign sfifo_esrng_err_sum = (|sfifo_esrng_err) ||
         err_code_test_bit[0];
  assign sfifo_distr_err_sum = (|sfifo_distr_err) ||
         err_code_test_bit[1];
  assign sfifo_observe_err_sum = (|sfifo_observe_err) ||
         err_code_test_bit[2];
  assign sfifo_esfinal_err_sum = (|sfifo_esfinal_err) ||
         err_code_test_bit[3];

  // The following test bits help normally diagnose the _type_ of
  // error when they are triggred by the fifo. However when
  // they are triggered by softwre they are not linked to a
  // particular sfifo and do not trigger an alert, unless
  // we capture them here.
  assign sfifo_test_err_sum = err_code_test_bit[28] ||
                              err_code_test_bit[29] ||
                              err_code_test_bit[30];

  assign es_ack_sm_err_sum = es_ack_sm_err ||
         err_code_test_bit[20];
  assign es_main_sm_err_sum = es_main_sm_err ||
         err_code_test_bit[21];
  assign es_cntr_err_sum = es_cntr_err ||
         err_code_test_bit[22];
  assign sha3_state_error_sum = sha3_state_error ||
         err_code_test_bit[23];
  assign sha3_rst_storage_err_sum = sha3_rst_storage_err ||
         err_code_test_bit[24];
  assign fifo_write_err_sum =
         sfifo_esrng_err[2] ||
         sfifo_observe_err[2] ||
         sfifo_esfinal_err[2] ||
         err_code_test_bit[28];
  assign fifo_read_err_sum =
         sfifo_esrng_err[1] ||
         sfifo_observe_err[1] ||
         sfifo_esfinal_err[1] ||
         err_code_test_bit[29];
  assign fifo_status_err_sum =
         sfifo_esrng_err[0] ||
         sfifo_observe_err[0] ||
         sfifo_esfinal_err[0] ||
         err_code_test_bit[30];

  // set the err code source bits
  assign hw2reg.err_code.sfifo_esrng_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_esrng_err.de = sfifo_esrng_err_sum;

  assign hw2reg.err_code.sfifo_distr_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_distr_err.de = sfifo_distr_err_sum;

  assign hw2reg.err_code.sfifo_observe_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_observe_err.de = sfifo_observe_err_sum;

  assign hw2reg.err_code.sfifo_esfinal_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_esfinal_err.de = sfifo_esfinal_err_sum;

  assign hw2reg.err_code.es_ack_sm_err.d = 1'b1;
  assign hw2reg.err_code.es_ack_sm_err.de = es_ack_sm_err_sum;

  assign hw2reg.err_code.es_main_sm_err.d = 1'b1;
  assign hw2reg.err_code.es_main_sm_err.de = es_main_sm_err_sum;

  assign hw2reg.err_code.es_cntr_err.d = 1'b1;
  assign hw2reg.err_code.es_cntr_err.de = es_cntr_err_sum;

  assign hw2reg.err_code.sha3_state_err.d = 1'b1;
  assign hw2reg.err_code.sha3_state_err.de = sha3_state_error_sum;

  assign hw2reg.err_code.sha3_rst_storage_err.d = 1'b1;
  assign hw2reg.err_code.sha3_rst_storage_err.de = sha3_rst_storage_err_sum;


 // set the err code type bits
  assign hw2reg.err_code.fifo_write_err.d = 1'b1;
  assign hw2reg.err_code.fifo_write_err.de = fifo_write_err_sum;

  assign hw2reg.err_code.fifo_read_err.d = 1'b1;
  assign hw2reg.err_code.fifo_read_err.de = fifo_read_err_sum;

  assign hw2reg.err_code.fifo_state_err.d = 1'b1;
  assign hw2reg.err_code.fifo_state_err.de = fifo_status_err_sum;

  // Error forcing
  for (genvar i = 0; i < 31; i = i+1) begin : gen_err_code_test_bit
    assign err_code_test_bit[i] = (reg2hw.err_code_test.q == i) && reg2hw.err_code_test.qe;
  end : gen_err_code_test_bit

  // alert - send all interrupt sources to the alert for the fatal case
  assign fatal_alert_o = (event_es_fatal_err |
                          sfifo_distr_int_err | sfifo_esrng_int_err |
                          sfifo_observe_int_err | sfifo_esfinal_int_err);

  // alert test
  assign recov_alert_test_o = {
    reg2hw.alert_test.recov_alert.q &&
    reg2hw.alert_test.recov_alert.qe
  };
  assign fatal_alert_test_o = {
    reg2hw.alert_test.fatal_alert.q &&
    reg2hw.alert_test.fatal_alert.qe
  };


  // set the debug status reg
  assign hw2reg.debug_status.entropy_fifo_depth.d = sfifo_esfinal_depth;
  assign hw2reg.debug_status.sha3_fsm.d = sha3_fsm;
  assign hw2reg.debug_status.sha3_block_pr.d = sha3_block_processed;
  assign hw2reg.debug_status.sha3_squeezing.d = sha3_squeezing;
  assign hw2reg.debug_status.sha3_absorbed.d =
    prim_mubi_pkg::mubi4_test_true_strict(sha3_absorbed) ? 1'b 1 : 1'b 0;
  assign hw2reg.debug_status.sha3_err.d = sha3_err_q;

  assign sha3_err_d =
         es_enable_fo[4] ? 1'b0 :
         {|sha3_err} ? 1'b1 :
         sha3_err_q;

  // state machine status
  assign hw2reg.debug_status.main_sm_idle.d = es_main_sm_idle;
  assign hw2reg.debug_status.main_sm_boot_done.d = boot_phase_done;
  assign hw2reg.main_sm_state.de = 1'b1;
  assign hw2reg.main_sm_state.d = es_main_sm_state;

  // fw override wr data status indication
  assign fw_ov_wr_fifo_full = fw_ov_mode_entropy_insert &&
                              (es_bypass_mode ? !pfifo_bypass_not_full : !pfifo_precon_not_full);

  assign hw2reg.fw_ov_wr_fifo_full.d = fw_ov_wr_fifo_full;


  //--------------------------------------------
  // receive in RNG bus input
  //--------------------------------------------

  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(RngBusWidth),
    .Pass(0),
    .Depth(2),
    .OutputZeroIfEmpty(0),
    .Secure(1)
  ) u_prim_fifo_sync_esrng (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (sfifo_esrng_clr),
    .wvalid_i   (sfifo_esrng_push),
    .wdata_i    (sfifo_esrng_wdata),
    .wready_o   (sfifo_esrng_not_full),
    .rvalid_o   (sfifo_esrng_not_empty),
    .rdata_o    (sfifo_esrng_rdata),
    .rready_i   (sfifo_esrng_pop),
    .full_o     (sfifo_esrng_full),
    .depth_o    (),
    .err_o      (sfifo_esrng_int_err)
  );

  // fifo controls
  // We can't handle any backpressure at this point. Unless the ENTROPY_SRC block is turned off,
  // the input coming from the noise source / RNG needs to be accepted without dropping samples.
  assign sfifo_esrng_push = es_enable_fo[5] && es_delayed_enable && es_rng_src_valid &&
                            rng_enable_q;

  assign sfifo_esrng_clr   = ~es_delayed_enable;
  assign sfifo_esrng_wdata = es_rng_bus;
  // We can't apply any backpressure at this point. Every sample is presented to the health tests
  // for exactly one clock cycle. If the receiving FIFO is full, the sample is dropped but the
  // health tests are still performed and the results accumulated.
  assign sfifo_esrng_pop = sfifo_esrng_not_empty;

  // fifo err
  // The esnrg FIFO must never be pushed when it's full as no backpressure can be applied to the
  // noise source / RNG. However, we can't raise an error and abort operation of the ENTROPY_SRC
  // block as this would mean a catastrophic failure of the whole chip. Instead we need to catch
  // this in simulation only.
  assign sfifo_esrng_err =
         {1'b0,
          (sfifo_esrng_pop && !sfifo_esrng_not_empty),
          (sfifo_esrng_full && !sfifo_esrng_not_empty) || sfifo_esrng_int_err};
  `ASSERT(RngBackpressureNotAllowed_A, sfifo_esrng_push |-> sfifo_esrng_not_full)

  // Read the health test data from the esrng FIFO.
  assign health_test_esbus = sfifo_esrng_rdata;
  // Perform the health tests whenever data is valid and the receiving FIFO is not being cleared.
  // This doesn't mean the receiving FIFO is pushed. The receiving FIFO is only pushed if it has
  // indeed space. This means in case of heavy backpressure, we keep testing the noise source
  // samples, but we drop them before the postht FIFO. If this happens, the window counter isn't
  // incremented. This way we can keep the number of bits going into the conditioner constant,
  // independent of potential backpressure within the pipeline.
  assign health_test_esbus_vld =
      rng_bit_en ? sfifo_esrng_not_empty && !pfifo_esbit_clr :
                   sfifo_esrng_not_empty && !pfifo_postht_clr;

  // Health test any data that comes in on the RNG interface.
  assign repcnt_active = 1'b1;
  assign repcnts_active = 1'b1;
  assign adaptp_active = 1'b1;
  assign bucket_active = 1'b1;
  assign markov_active = 1'b1;
  assign extht_active = 1'b1;

  // Only reset health tests on re-enable
  assign health_test_clr = module_en_pulse_fo[0];

  assign health_test_fips_window = reg2hw.health_test_windows.fips_window.q;
  assign health_test_bypass_window = reg2hw.health_test_windows.bypass_window.q;

  assign repcnt_fips_threshold = reg2hw.repcnt_thresholds.fips_thresh.q;
  assign repcnt_fips_threshold_wr = reg2hw.repcnt_thresholds.fips_thresh.qe;
  assign hw2reg.repcnt_thresholds.fips_thresh.d = repcnt_fips_threshold_oneway;
  assign repcnt_bypass_threshold = reg2hw.repcnt_thresholds.bypass_thresh.q;
  assign repcnt_bypass_threshold_wr = reg2hw.repcnt_thresholds.bypass_thresh.qe;
  assign hw2reg.repcnt_thresholds.bypass_thresh.d = repcnt_bypass_threshold_oneway;

  assign repcnts_fips_threshold = reg2hw.repcnts_thresholds.fips_thresh.q;
  assign repcnts_fips_threshold_wr = reg2hw.repcnts_thresholds.fips_thresh.qe;
  assign hw2reg.repcnts_thresholds.fips_thresh.d = repcnts_fips_threshold_oneway;
  assign repcnts_bypass_threshold = reg2hw.repcnts_thresholds.bypass_thresh.q;
  assign repcnts_bypass_threshold_wr = reg2hw.repcnts_thresholds.bypass_thresh.qe;
  assign hw2reg.repcnts_thresholds.bypass_thresh.d = repcnts_bypass_threshold_oneway;


  assign adaptp_hi_fips_threshold = reg2hw.adaptp_hi_thresholds.fips_thresh.q;
  assign adaptp_hi_fips_threshold_wr = reg2hw.adaptp_hi_thresholds.fips_thresh.qe;
  assign hw2reg.adaptp_hi_thresholds.fips_thresh.d = adaptp_hi_fips_threshold_oneway;
  assign adaptp_hi_bypass_threshold = reg2hw.adaptp_hi_thresholds.bypass_thresh.q;
  assign adaptp_hi_bypass_threshold_wr = reg2hw.adaptp_hi_thresholds.bypass_thresh.qe;
  assign hw2reg.adaptp_hi_thresholds.bypass_thresh.d = adaptp_hi_bypass_threshold_oneway;

  assign adaptp_lo_fips_threshold = reg2hw.adaptp_lo_thresholds.fips_thresh.q;
  assign adaptp_lo_fips_threshold_wr = reg2hw.adaptp_lo_thresholds.fips_thresh.qe;
  assign hw2reg.adaptp_lo_thresholds.fips_thresh.d = adaptp_lo_fips_threshold_oneway;
  assign adaptp_lo_bypass_threshold = reg2hw.adaptp_lo_thresholds.bypass_thresh.q;
  assign adaptp_lo_bypass_threshold_wr = reg2hw.adaptp_lo_thresholds.bypass_thresh.qe;
  assign hw2reg.adaptp_lo_thresholds.bypass_thresh.d = adaptp_lo_bypass_threshold_oneway;


  assign bucket_fips_threshold = reg2hw.bucket_thresholds.fips_thresh.q;
  assign bucket_fips_threshold_wr = reg2hw.bucket_thresholds.fips_thresh.qe;
  assign hw2reg.bucket_thresholds.fips_thresh.d = bucket_fips_threshold_oneway;
  assign bucket_bypass_threshold = reg2hw.bucket_thresholds.bypass_thresh.q;
  assign bucket_bypass_threshold_wr = reg2hw.bucket_thresholds.bypass_thresh.qe;
  assign hw2reg.bucket_thresholds.bypass_thresh.d = bucket_bypass_threshold_oneway;


  assign markov_hi_fips_threshold = reg2hw.markov_hi_thresholds.fips_thresh.q;
  assign markov_hi_fips_threshold_wr = reg2hw.markov_hi_thresholds.fips_thresh.qe;
  assign hw2reg.markov_hi_thresholds.fips_thresh.d = markov_hi_fips_threshold_oneway;
  assign markov_hi_bypass_threshold = reg2hw.markov_hi_thresholds.bypass_thresh.q;
  assign markov_hi_bypass_threshold_wr = reg2hw.markov_hi_thresholds.bypass_thresh.qe;
  assign hw2reg.markov_hi_thresholds.bypass_thresh.d = markov_hi_bypass_threshold_oneway;

  assign markov_lo_fips_threshold = reg2hw.markov_lo_thresholds.fips_thresh.q;
  assign markov_lo_fips_threshold_wr = reg2hw.markov_lo_thresholds.fips_thresh.qe;
  assign hw2reg.markov_lo_thresholds.fips_thresh.d = markov_lo_fips_threshold_oneway;
  assign markov_lo_bypass_threshold = reg2hw.markov_lo_thresholds.bypass_thresh.q;
  assign markov_lo_bypass_threshold_wr = reg2hw.markov_lo_thresholds.bypass_thresh.qe;
  assign hw2reg.markov_lo_thresholds.bypass_thresh.d = markov_lo_bypass_threshold_oneway;


  assign extht_hi_fips_threshold = reg2hw.extht_hi_thresholds.fips_thresh.q;
  assign extht_hi_fips_threshold_wr = reg2hw.extht_hi_thresholds.fips_thresh.qe;
  assign hw2reg.extht_hi_thresholds.fips_thresh.d = extht_hi_fips_threshold_oneway;
  assign extht_hi_bypass_threshold = reg2hw.extht_hi_thresholds.bypass_thresh.q;
  assign extht_hi_bypass_threshold_wr = reg2hw.extht_hi_thresholds.bypass_thresh.qe;
  assign hw2reg.extht_hi_thresholds.bypass_thresh.d = extht_hi_bypass_threshold_oneway;

  assign extht_lo_fips_threshold = reg2hw.extht_lo_thresholds.fips_thresh.q;
  assign extht_lo_fips_threshold_wr = reg2hw.extht_lo_thresholds.fips_thresh.qe;
  assign hw2reg.extht_lo_thresholds.fips_thresh.d = extht_lo_fips_threshold_oneway;
  assign extht_lo_bypass_threshold = reg2hw.extht_lo_thresholds.bypass_thresh.q;
  assign extht_lo_bypass_threshold_wr = reg2hw.extht_lo_thresholds.bypass_thresh.qe;
  assign hw2reg.extht_lo_thresholds.bypass_thresh.d = extht_lo_bypass_threshold_oneway;


  assign health_test_window = es_bypass_mode ? health_test_bypass_window : health_test_fips_window;
  // Multiply the health test window by four if we are using the single lane mode.
  // In single lane mode 4 times as many symbols are tested for the same amount of entropy.
  assign health_test_window_scaled = rng_bit_en ? {health_test_window, 2'b0} :
                                                  {2'b0, health_test_window};

  // Window sizes other than 384 bits (the seed length) are currently not tested nor supported in
  // bypass or boot-time mode.
  `ASSERT(EsBootTimeHtWindowSizeSupported_A,
      main_sm_enable && es_bypass_mode && !fw_ov_mode_entropy_insert
      |-> health_test_bypass_window == HalfRegWidth'(SeedLen/4))

  //------------------------------
  // repcnt one-way thresholds
  //------------------------------
  assign repcnt_threshold = es_bypass_mode ? repcnt_bypass_threshold_oneway :
         repcnt_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_repcnt_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (repcnt_fips_threshold_wr),
    .value_i             (repcnt_fips_threshold),
    .value_o             (repcnt_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_repcnt_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (repcnt_bypass_threshold_wr),
    .value_i             (repcnt_bypass_threshold),
    .value_o             (repcnt_bypass_threshold_oneway)
  );

  //------------------------------
  // repcnts one-way thresholds
  //------------------------------
  assign repcnts_threshold = es_bypass_mode ? repcnts_bypass_threshold_oneway :
         repcnts_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_repcnts_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (repcnts_fips_threshold_wr),
    .value_i             (repcnts_fips_threshold),
    .value_o             (repcnts_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_repcnts_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (repcnts_bypass_threshold_wr),
    .value_i             (repcnts_bypass_threshold),
    .value_o             (repcnts_bypass_threshold_oneway)
  );


  //------------------------------
  // adaptp one-way thresholds
  //------------------------------
  assign adaptp_hi_threshold = es_bypass_mode ? adaptp_hi_bypass_threshold_oneway :
         adaptp_hi_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_adaptp_hi_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (adaptp_hi_fips_threshold_wr),
    .value_i             (adaptp_hi_fips_threshold),
    .value_o             (adaptp_hi_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_adaptp_hi_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (adaptp_hi_bypass_threshold_wr),
    .value_i             (adaptp_hi_bypass_threshold),
    .value_o             (adaptp_hi_bypass_threshold_oneway)
  );

  assign adaptp_lo_threshold = es_bypass_mode ? adaptp_lo_bypass_threshold_oneway :
         adaptp_lo_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_adaptp_lo_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (adaptp_lo_fips_threshold_wr),
    .value_i             (adaptp_lo_fips_threshold),
    .value_o             (adaptp_lo_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_adaptp_lo_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (adaptp_lo_bypass_threshold_wr),
    .value_i             (adaptp_lo_bypass_threshold),
    .value_o             (adaptp_lo_bypass_threshold_oneway)
  );


  //------------------------------
  // bucket one-way thresholds
  //------------------------------
  assign bucket_threshold = es_bypass_mode ? bucket_bypass_threshold_oneway :
         bucket_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_bucket_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (bucket_fips_threshold_wr),
    .value_i             (bucket_fips_threshold),
    .value_o             (bucket_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_bucket_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (bucket_bypass_threshold_wr),
    .value_i             (bucket_bypass_threshold),
    .value_o             (bucket_bypass_threshold_oneway)
  );


  //------------------------------
  // markov one-way thresholds
  //------------------------------
  assign markov_hi_threshold = es_bypass_mode ? markov_hi_bypass_threshold_oneway :
         markov_hi_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_markov_hi_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (markov_hi_fips_threshold_wr),
    .value_i             (markov_hi_fips_threshold),
    .value_o             (markov_hi_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_markov_hi_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (markov_hi_bypass_threshold_wr),
    .value_i             (markov_hi_bypass_threshold),
    .value_o             (markov_hi_bypass_threshold_oneway)
  );

  assign markov_lo_threshold = es_bypass_mode ? markov_lo_bypass_threshold_oneway :
         markov_lo_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_markov_lo_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (markov_lo_fips_threshold_wr),
    .value_i             (markov_lo_fips_threshold),
    .value_o             (markov_lo_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_markov_lo_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (markov_lo_bypass_threshold_wr),
    .value_i             (markov_lo_bypass_threshold),
    .value_o             (markov_lo_bypass_threshold_oneway)
  );


  //------------------------------
  // extht one-way thresholds
  //------------------------------
  assign extht_hi_threshold = es_bypass_mode ? extht_hi_bypass_threshold_oneway :
         extht_hi_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_extht_hi_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (extht_hi_fips_threshold_wr),
    .value_i             (extht_hi_fips_threshold),
    .value_o             (extht_hi_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_extht_hi_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (extht_hi_bypass_threshold_wr),
    .value_i             (extht_hi_bypass_threshold),
    .value_o             (extht_hi_bypass_threshold_oneway)
  );


  assign extht_lo_threshold = es_bypass_mode ? extht_lo_bypass_threshold_oneway :
         extht_lo_fips_threshold_oneway;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_extht_lo_thresh_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (extht_lo_fips_threshold_wr),
    .value_i             (extht_lo_fips_threshold),
    .value_o             (extht_lo_fips_threshold_oneway)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_extht_lo_thresh_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (1'b0),
    .event_i             (extht_lo_bypass_threshold_wr),
    .value_i             (extht_lo_bypass_threshold),
    .value_o             (extht_lo_bypass_threshold_oneway)
  );



  //------------------------------
  // misc control settings
  //------------------------------

  assign event_es_health_test_failed = es_main_sm_alert;

  assign event_es_observe_fifo_ready = observe_fifo_thresh_met;

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_es_route;
  mubi4_t [1:0] mubi_es_route_fanout;
  assign mubi_es_route = mubi4_t'(reg2hw.entropy_control.es_route.q);
  assign es_route_pfe = mubi4_test_true_strict(mubi_es_route_fanout[0]);
  assign es_route_pfa = mubi4_test_invalid(mubi_es_route_fanout[1]);
  assign hw2reg.recov_alert_sts.es_route_field_alert.de = es_route_pfa;
  assign hw2reg.recov_alert_sts.es_route_field_alert.d  = es_route_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_es_route (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_es_route),
    .mubi_o(mubi_es_route_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_es_type;
  mubi4_t [1:0] mubi_es_type_fanout;
  assign mubi_es_type = mubi4_t'(reg2hw.entropy_control.es_type.q);
  assign es_type_pfe = mubi4_test_true_strict(mubi_es_type_fanout[0]);
  assign es_type_pfa = mubi4_test_invalid(mubi_es_type_fanout[1]);
  assign hw2reg.recov_alert_sts.es_type_field_alert.de = es_type_pfa;
  assign hw2reg.recov_alert_sts.es_type_field_alert.d  = es_type_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_es_type (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_es_type),
    .mubi_o(mubi_es_type_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_thresh_scope;
  assign mubi_thresh_scope = mubi4_t'(reg2hw.conf.threshold_scope.q);
  assign threshold_scope_pfe = mubi4_test_true_strict(mubi_thresh_scope);
  assign threshold_scope_pfa = mubi4_test_invalid(mubi_thresh_scope);
  assign hw2reg.recov_alert_sts.threshold_scope_field_alert.de = threshold_scope_pfa;
  assign hw2reg.recov_alert_sts.threshold_scope_field_alert.d  = threshold_scope_pfa;

  assign es_route_to_sw = es_route_pfe;
  assign es_bypass_to_sw = es_type_pfe;
  assign threshold_scope = threshold_scope_pfe;

  // The es_bypass_mode signal determines whether the conditioner is bypassed or not.
  // It also determines which thresholds are used and which watermarks are recorded.
  // The conditioner can be bypassed by either disabling fips_enable_pfe or by enabling
  // both es_bypass_to_sw and es_route_to_sw.
  // The combination of es_bypass_to_sw and es_route_to_sw allows for four distinct cases:
  //  _________________ ________________
  // |                 |                |
  // | es_bypass_to_sw | es_route_to_sw |
  // |_________________|________________|
  // |                 |                |
  // |        0        |       0        | In this case the entropy passes through the conditioner
  // |_________________|________________| and the entropy is forwarded to the HW endpoints.
  // |                 |                |
  // |        0        |       1        | In this case the entropy passes through the conditioner
  // |_________________|________________| and the entropy is forwarded to software.
  // |                 |                |
  // |        1        |       0        | In this case nothing happens and whether the conditioner
  // |_________________|________________| is bypassed solely depends on fips_enable_pfe.
  // |                 |                |
  // |        1        |       1        | In this case the conditioner is bypassed and the entropy
  // |_________________|________________| is forwarded to software.

  assign es_bypass_mode = (!fips_enable_pfe) || (es_bypass_to_sw && es_route_to_sw);

  // send off to AST RNG for possibly faster entropy generation
  assign rng_fips_o = rng_fips_pfe;

  //--------------------------------------------
  // common health test window counter
  //--------------------------------------------

  // Window counter
  // SEC_CM: CTR.REDUN

  // We only increment the counter if the currently tested sample can be pushed to the correct FIFO
  // following the health tests. This is required to keep the number of samples passed to the
  // conditioner constant also when experiencing backpressure from the conditioner. At the same
  // time, we're not allowed to drop samples before the health testing. This means the number of
  // tested samples might be slightly bigger than the number of samples fed into the conditioner.
  assign window_cntr_incr_en =
      rng_bit_en ? pfifo_esbit_push  && pfifo_esbit_not_full  && !pfifo_esbit_clr :
                   pfifo_postht_push && pfifo_postht_not_full && !pfifo_postht_clr;

  prim_count #(
    .Width(WINDOW_CNTR_WIDTH)
  ) u_prim_count_window_cntr (
    .clk_i,
    .rst_ni,
    .clr_i(!es_delayed_enable),
    .set_i(health_test_done_pulse),
    .set_cnt_i(WINDOW_CNTR_WIDTH'(0)),
    .incr_en_i(window_cntr_incr_en),
    .decr_en_i(1'b0),
    .step_i(WINDOW_CNTR_WIDTH'(1)),
    .commit_i(1'b1),
    .cnt_o(window_cntr),
    .cnt_after_commit_o(),
    .err_o(window_cntr_err)
  );

  // Window wrap condition
  assign health_test_done_pulse = (window_cntr >= health_test_window_scaled);

  // Summary of counter errors
  assign es_cntr_err =
         (window_cntr_err ||
          repcnt_cntr_err ||
          repcnts_cntr_err ||
          adaptp_cntr_err ||
          bucket_cntr_err ||
          markov_cntr_err ||
          repcnt_fails_cntr_err ||
          repcnt_alert_cntr_err ||
          repcnts_fails_cntr_err ||
          repcnts_alert_cntr_err ||
          adaptp_hi_fails_cntr_err ||
          adaptp_lo_fails_cntr_err ||
          adaptp_hi_alert_cntr_err ||
          adaptp_lo_alert_cntr_err ||
          bucket_fails_cntr_err ||
          bucket_alert_cntr_err ||
          markov_hi_fails_cntr_err ||
          markov_lo_fails_cntr_err ||
          markov_hi_alert_cntr_err ||
          markov_lo_alert_cntr_err ||
          extht_hi_fails_cntr_err ||
          extht_lo_fails_cntr_err ||
          extht_hi_alert_cntr_err ||
          extht_lo_alert_cntr_err ||
          any_fails_cntr_err ||
          sha3_count_error);

  //--------------------------------------------
  // repetitive count test
  //--------------------------------------------

  // SEC_CM: RNG.BKGN_CHK
  entropy_src_repcnt_ht #(
    .RegWidth(HalfRegWidth),
    .RngBusWidth(RngBusWidth)
  ) u_entropy_src_repcnt_ht (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .entropy_bit_i       (health_test_esbus),
    .entropy_bit_vld_i   (health_test_esbus_vld),
    .rng_bit_en_i        (rng_bit_en),
    .rng_bit_sel_i       (rng_bit_sel),
    .clear_i             (health_test_clr),
    .active_i            (repcnt_active),
    .thresh_i            (repcnt_threshold),
    .test_cnt_o          (repcnt_event_cnt),
    .test_fail_pulse_o   (repcnt_fail_pulse),
    .count_err_o         (repcnt_cntr_err)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_repcnt_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (!es_bypass_mode),
    .value_i             (repcnt_event_cnt),
    .value_o             (repcnt_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_repcnt_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (es_bypass_mode),
    .value_i             (repcnt_event_cnt),
    .value_o             (repcnt_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_repcnt (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (repcnt_fail_pulse),
    .value_o             (repcnt_total_fails),
    .err_o               (repcnt_fails_cntr_err)
  );

  assign hw2reg.repcnt_hi_watermarks.fips_watermark.d = repcnt_event_hwm_fips;
  assign hw2reg.repcnt_hi_watermarks.bypass_watermark.d = repcnt_event_hwm_bypass;
  assign hw2reg.repcnt_total_fails.d = repcnt_total_fails;

  //--------------------------------------------
  // repetitive count symbol test
  //--------------------------------------------

  // SEC_CM: RNG.BKGN_CHK
  entropy_src_repcnts_ht #(
    .RegWidth(HalfRegWidth),
    .RngBusWidth(RngBusWidth)
  ) u_entropy_src_repcnts_ht (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .entropy_bit_i       (health_test_esbus),
    .entropy_bit_vld_i   (health_test_esbus_vld),
    .clear_i             (health_test_clr),
    .active_i            (repcnts_active),
    .thresh_i            (repcnts_threshold),
    .test_cnt_o          (repcnts_event_cnt),
    .test_fail_pulse_o   (repcnts_fail_pulse),
    .count_err_o         (repcnts_cntr_err)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_repcnts_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (!es_bypass_mode),
    .value_i             (repcnts_event_cnt),
    .value_o             (repcnts_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_repcnts_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (es_bypass_mode),
    .value_i             (repcnts_event_cnt),
    .value_o             (repcnts_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_repcnts (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (repcnts_fail_pulse),
    .value_o             (repcnts_total_fails),
    .err_o               (repcnts_fails_cntr_err)
  );

  assign hw2reg.repcnts_hi_watermarks.fips_watermark.d = repcnts_event_hwm_fips;
  assign hw2reg.repcnts_hi_watermarks.bypass_watermark.d = repcnts_event_hwm_bypass;
  assign hw2reg.repcnts_total_fails.d = repcnts_total_fails;

  //--------------------------------------------
  // adaptive proportion test
  //--------------------------------------------

  // SEC_CM: RNG.BKGN_CHK
  entropy_src_adaptp_ht #(
    .RegWidth(HalfRegWidth),
    .RngBusWidth(RngBusWidth)
  ) u_entropy_src_adaptp_ht (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .entropy_bit_i       (health_test_esbus),
    .entropy_bit_vld_i   (health_test_esbus_vld),
    .rng_bit_en_i        (rng_bit_en),
    .rng_bit_sel_i       (rng_bit_sel),
    .clear_i             (health_test_clr),
    .active_i            (adaptp_active),
    .thresh_hi_i         (adaptp_hi_threshold),
    .thresh_lo_i         (adaptp_lo_threshold),
    .window_wrap_pulse_i (health_test_done_pulse),
    .threshold_scope_i   (threshold_scope),
    .test_cnt_hi_o       (adaptp_hi_event_cnt),
    .test_cnt_lo_o       (adaptp_lo_event_cnt),
    .test_fail_hi_pulse_o(adaptp_hi_fail_pulse),
    .test_fail_lo_pulse_o(adaptp_lo_fail_pulse),
    .count_err_o         (adaptp_cntr_err)
  );


  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_adaptp_hi_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && !es_bypass_mode),
    .value_i             (adaptp_hi_event_cnt),
    .value_o             (adaptp_hi_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_adaptp_hi_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && es_bypass_mode),
    .value_i             (adaptp_hi_event_cnt),
    .value_o             (adaptp_hi_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_adaptp_hi (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (adaptp_hi_fail_pulse),
    .value_o             (adaptp_hi_total_fails),
    .err_o               (adaptp_hi_fails_cntr_err)
  );


  assign hw2reg.adaptp_hi_watermarks.fips_watermark.d = adaptp_hi_event_hwm_fips;
  assign hw2reg.adaptp_hi_watermarks.bypass_watermark.d = adaptp_hi_event_hwm_bypass;
  assign hw2reg.adaptp_hi_total_fails.d = adaptp_hi_total_fails;


  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_adaptp_lo_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && !es_bypass_mode),
    .value_i             (adaptp_lo_event_cnt),
    .value_o             (adaptp_lo_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_adaptp_lo_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && es_bypass_mode),
    .value_i             (adaptp_lo_event_cnt),
    .value_o             (adaptp_lo_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_adaptp_lo (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (adaptp_lo_fail_pulse),
    .value_o             (adaptp_lo_total_fails),
    .err_o               (adaptp_lo_fails_cntr_err)
  );

  assign hw2reg.adaptp_lo_watermarks.fips_watermark.d = adaptp_lo_event_hwm_fips;
  assign hw2reg.adaptp_lo_watermarks.bypass_watermark.d = adaptp_lo_event_hwm_bypass;
  assign hw2reg.adaptp_lo_total_fails.d = adaptp_lo_total_fails;


  //--------------------------------------------
  // bucket test
  //--------------------------------------------

  // SEC_CM: RNG.BKGN_CHK
  entropy_src_bucket_ht #(
    .RegWidth(HalfRegWidth),
    .RngBusWidth(RngBusWidth)
  ) u_entropy_src_bucket_ht (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .entropy_bit_i       (health_test_esbus),
    .entropy_bit_vld_i   (health_test_esbus_vld),
    .clear_i             (health_test_clr),
    .active_i            (bucket_active),
    .thresh_i            (bucket_threshold),
    .window_wrap_pulse_i (health_test_done_pulse),
    .test_cnt_o          (bucket_event_cnt),
    .test_fail_pulse_o   (bucket_fail_pulse),
    .count_err_o         (bucket_cntr_err)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_bucket_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && !es_bypass_mode),
    .value_i             (bucket_event_cnt),
    .value_o             (bucket_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_bucket_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && es_bypass_mode),
    .value_i             (bucket_event_cnt),
    .value_o             (bucket_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_bucket (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (bucket_fail_pulse),
    .value_o             (bucket_total_fails),
    .err_o               (bucket_fails_cntr_err)
  );

  assign hw2reg.bucket_hi_watermarks.fips_watermark.d = bucket_event_hwm_fips;
  assign hw2reg.bucket_hi_watermarks.bypass_watermark.d = bucket_event_hwm_bypass;
  assign hw2reg.bucket_total_fails.d = bucket_total_fails;


  //--------------------------------------------
  // Markov test
  //--------------------------------------------

  // SEC_CM: RNG.BKGN_CHK
  entropy_src_markov_ht #(
    .RegWidth(HalfRegWidth),
    .RngBusWidth(RngBusWidth)
  ) u_entropy_src_markov_ht (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .entropy_bit_i       (health_test_esbus),
    .entropy_bit_vld_i   (health_test_esbus_vld),
    .rng_bit_en_i        (rng_bit_en),
    .rng_bit_sel_i       (rng_bit_sel),
    .clear_i             (health_test_clr),
    .active_i            (markov_active),
    .thresh_hi_i         (markov_hi_threshold),
    .thresh_lo_i         (markov_lo_threshold),
    .window_wrap_pulse_i (health_test_done_pulse),
    .threshold_scope_i   (threshold_scope),
    .test_cnt_hi_o       (markov_hi_event_cnt),
    .test_cnt_lo_o       (markov_lo_event_cnt),
    .test_fail_hi_pulse_o (markov_hi_fail_pulse),
    .test_fail_lo_pulse_o (markov_lo_fail_pulse),
    .count_err_o         (markov_cntr_err)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_markov_hi_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && !es_bypass_mode),
    .value_i             (markov_hi_event_cnt),
    .value_o             (markov_hi_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_markov_hi_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && es_bypass_mode),
    .value_i             (markov_hi_event_cnt),
    .value_o             (markov_hi_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_markov_hi (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (markov_hi_fail_pulse),
    .value_o             (markov_hi_total_fails),
    .err_o               (markov_hi_fails_cntr_err)
  );

  assign hw2reg.markov_hi_watermarks.fips_watermark.d = markov_hi_event_hwm_fips;
  assign hw2reg.markov_hi_watermarks.bypass_watermark.d = markov_hi_event_hwm_bypass;
  assign hw2reg.markov_hi_total_fails.d = markov_hi_total_fails;


  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_markov_lo_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && !es_bypass_mode),
    .value_i             (markov_lo_event_cnt),
    .value_o             (markov_lo_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_markov_lo_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (health_test_done_pulse && es_bypass_mode),
    .value_i             (markov_lo_event_cnt),
    .value_o             (markov_lo_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_markov_lo (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (markov_lo_fail_pulse),
    .value_o             (markov_lo_total_fails),
    .err_o               (markov_lo_fails_cntr_err)
  );

  assign hw2reg.markov_lo_watermarks.fips_watermark.d = markov_lo_event_hwm_fips;
  assign hw2reg.markov_lo_watermarks.bypass_watermark.d = markov_lo_event_hwm_bypass;
  assign hw2reg.markov_lo_total_fails.d = markov_lo_total_fails;


  //--------------------------------------------
  // External health test
  //--------------------------------------------

  // set outputs to external health test
  assign entropy_src_xht_o.entropy_bit = health_test_esbus;
  assign entropy_src_xht_o.entropy_bit_valid = health_test_esbus_vld;
  assign entropy_src_xht_o.rng_bit_en = rng_bit_en;
  assign entropy_src_xht_o.rng_bit_sel = rng_bit_sel;
  assign entropy_src_xht_o.clear = health_test_clr;
  assign entropy_src_xht_o.active = extht_active;
  assign entropy_src_xht_o.thresh_hi = extht_hi_threshold;
  assign entropy_src_xht_o.thresh_lo = extht_lo_threshold;
  assign entropy_src_xht_o.window_wrap_pulse = health_test_done_pulse;
  assign entropy_src_xht_o.health_test_window = health_test_window_scaled;
  assign entropy_src_xht_o.threshold_scope = threshold_scope;
  // get inputs from external health test
  assign extht_event_cnt_hi = entropy_src_xht_i.test_cnt_hi;
  assign extht_event_cnt_lo = entropy_src_xht_i.test_cnt_lo;
  assign extht_hi_fail_pulse = entropy_src_xht_i.test_fail_hi_pulse;
  assign extht_lo_fail_pulse = entropy_src_xht_i.test_fail_lo_pulse;
  assign extht_cont_test = entropy_src_xht_i.continuous_test;

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_extht_hi_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             ((extht_cont_test || health_test_done_pulse) && !es_bypass_mode),
    .value_i             (extht_event_cnt_hi),
    .value_o             (extht_hi_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(1)
  ) u_entropy_src_watermark_reg_extht_hi_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             ((extht_cont_test || health_test_done_pulse) && es_bypass_mode),
    .value_i             (extht_event_cnt_hi),
    .value_o             (extht_hi_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_extht_hi (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (extht_hi_fail_pulse),
    .value_o             (extht_hi_total_fails),
    .err_o               (extht_hi_fails_cntr_err)
  );


  assign hw2reg.extht_hi_watermarks.fips_watermark.d = extht_hi_event_hwm_fips;
  assign hw2reg.extht_hi_watermarks.bypass_watermark.d = extht_hi_event_hwm_bypass;
  assign hw2reg.extht_hi_total_fails.d = extht_hi_total_fails;


  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_extht_lo_fips (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             ((extht_cont_test || health_test_done_pulse) && !es_bypass_mode),
    .value_i             (extht_event_cnt_lo),
    .value_o             (extht_lo_event_hwm_fips)
  );

  entropy_src_watermark_reg #(
    .RegWidth(HalfRegWidth),
    .HighWatermark(0)
  ) u_entropy_src_watermark_reg_extht_lo_bypass (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             ((extht_cont_test || health_test_done_pulse) && es_bypass_mode),
    .value_i             (extht_event_cnt_lo),
    .value_o             (extht_lo_event_hwm_bypass)
  );

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(FullRegWidth)
  ) u_entropy_src_cntr_reg_extht_lo (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (health_test_clr),
    .event_i             (extht_lo_fail_pulse),
    .value_o             (extht_lo_total_fails),
    .err_o               (extht_lo_fails_cntr_err)
  );

  assign hw2reg.extht_lo_watermarks.fips_watermark.d = extht_lo_event_hwm_fips;
  assign hw2reg.extht_lo_watermarks.bypass_watermark.d = extht_lo_event_hwm_bypass;
  assign hw2reg.extht_lo_total_fails.d = extht_lo_total_fails;


  //--------------------------------------------
  // summary and alert registers
  //--------------------------------------------

  assign alert_cntrs_clr = health_test_clr || rst_alert_cntr;

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(HalfRegWidth)
  ) u_entropy_src_cntr_reg_any_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (any_fail_pulse),
    .value_o             (any_fail_count),
    .err_o               (any_fails_cntr_err)
  );

  assign any_fail_pulse =
         repcnt_fail_pulse ||
         repcnts_fail_pulse ||
         adaptp_hi_fail_pulse || adaptp_lo_fail_pulse ||
         bucket_fail_pulse ||
         markov_hi_fail_pulse || markov_lo_fail_pulse ||
         extht_hi_fail_pulse || extht_lo_fail_pulse;

  assign ht_failed_d =
         (!es_enable_fo[6]) ? 1'b0 :
         ht_done_pulse_q ? 1'b0 :
         any_fail_pulse ? 1'b1 :
         ht_failed_q;


  // delay health pulse so that main_sm will
  // get the correct threshold value comparisons
  assign ht_done_pulse_d = health_test_done_pulse;

  assign hw2reg.alert_summary_fail_counts.d = any_fail_count;

  // signal an alert
  // SEC_CM: CONFIG.REDUN
  assign alert_threshold = reg2hw.alert_threshold.alert_threshold.q;
  assign alert_threshold_inv = reg2hw.alert_threshold.alert_threshold_inv.q;
  assign es_thresh_cfg_alert = (~alert_threshold_inv != alert_threshold);

  assign alert_threshold_fail =
         ((any_fail_count >= ~alert_threshold_inv) && (~alert_threshold_inv != '0)) ||
         (any_fail_count >= alert_threshold) && (alert_threshold != '0);


  prim_edge_detector #(
    .Width(1),
    .ResetValue(0),
    .EnSync(0)
  ) u_prim_edge_detector_recov_alert (
    .clk_i,
    .rst_ni,
    .d_i(recov_alert_state),
    .q_sync_o(),
    .q_posedge_pulse_o(recov_alert_o),
    .q_negedge_pulse_o()
  );

  assign recov_alert_state =
         es_enable_pfa ||
         fips_enable_pfa ||
         fips_flag_pfa ||
         rng_fips_pfa ||
         entropy_data_reg_en_pfa ||
         threshold_scope_pfa ||
         rng_bit_enable_pfa ||
         fw_ov_mode_pfa ||
         fw_ov_entropy_insert_pfa ||
         fw_ov_sha3_start_pfa ||
         es_route_pfa ||
         es_type_pfa ||
         es_main_sm_alert ||
         es_bus_cmp_alert ||
         es_thresh_cfg_alert ||
         es_fw_ov_wr_alert ||
         es_fw_ov_disable_alert ||
         postht_entropy_drop_alert;

  assign hw2reg.recov_alert_sts.es_main_sm_alert.de = es_main_sm_alert;
  assign hw2reg.recov_alert_sts.es_main_sm_alert.d  = es_main_sm_alert;

  assign hw2reg.recov_alert_sts.es_bus_cmp_alert.de = es_bus_cmp_alert;
  assign hw2reg.recov_alert_sts.es_bus_cmp_alert.d  = es_bus_cmp_alert;

  assign hw2reg.recov_alert_sts.es_thresh_cfg_alert.de = es_thresh_cfg_alert;
  assign hw2reg.recov_alert_sts.es_thresh_cfg_alert.d  = es_thresh_cfg_alert;

  assign hw2reg.recov_alert_sts.es_fw_ov_wr_alert.de = es_fw_ov_wr_alert;
  assign hw2reg.recov_alert_sts.es_fw_ov_wr_alert.d  = es_fw_ov_wr_alert;

  assign hw2reg.recov_alert_sts.es_fw_ov_disable_alert.de = es_fw_ov_disable_alert;
  assign hw2reg.recov_alert_sts.es_fw_ov_disable_alert.d  = es_fw_ov_disable_alert;

  // repcnt fail counter
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_repcnt_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (repcnt_fail_pulse),
    .value_o             (repcnt_fail_count),
    .err_o               (repcnt_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.repcnt_fail_count.d = repcnt_fail_count;

  // repcnts fail counter
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_repcnts_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (repcnts_fail_pulse),
    .value_o             (repcnts_fail_count),
    .err_o               (repcnts_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.repcnts_fail_count.d = repcnts_fail_count;

  // adaptp fail counter hi and lo
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_adaptp_hi_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (adaptp_hi_fail_pulse),
    .value_o             (adaptp_hi_fail_count),
    .err_o               (adaptp_hi_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.adaptp_hi_fail_count.d = adaptp_hi_fail_count;

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_adaptp_lo_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (adaptp_lo_fail_pulse),
    .value_o             (adaptp_lo_fail_count),
    .err_o               (adaptp_lo_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.adaptp_lo_fail_count.d = adaptp_lo_fail_count;

  // bucket fail counter
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_bucket_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (bucket_fail_pulse),
    .value_o             (bucket_fail_count),
    .err_o               (bucket_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.bucket_fail_count.d = bucket_fail_count;


  // markov fail counter hi and lo
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_markov_hi_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (markov_hi_fail_pulse),
    .value_o             (markov_hi_fail_count),
    .err_o               (markov_hi_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.markov_hi_fail_count.d = markov_hi_fail_count;

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_markov_lo_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (markov_lo_fail_pulse),
    .value_o             (markov_lo_fail_count),
    .err_o               (markov_lo_alert_cntr_err)
  );

  assign hw2reg.alert_fail_counts.markov_lo_fail_count.d = markov_lo_fail_count;

  // extht fail counter hi and lo
  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_extht_hi_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (extht_hi_fail_pulse),
    .value_o             (extht_hi_fail_count),
    .err_o               (extht_hi_alert_cntr_err)
  );

  assign hw2reg.extht_fail_counts.extht_hi_fail_count.d = extht_hi_fail_count;

  // SEC_CM: CTR.REDUN
  entropy_src_cntr_reg #(
    .RegWidth(EighthRegWidth)
  ) u_entropy_src_cntr_reg_extht_lo_alert_fails (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .clear_i             (alert_cntrs_clr),
    .event_i             (extht_lo_fail_pulse),
    .value_o             (extht_lo_fail_count),
    .err_o               (extht_lo_alert_cntr_err)
  );

  assign hw2reg.extht_fail_counts.extht_lo_fail_count.d = extht_lo_fail_count;


  //------------------------------------------------------------------
  // Signal a recoverable alert when dropping tested entropy bits.
  //------------------------------------------------------------------

  // Post-health test entropy bits can be dropped from the pipeline in case of e.g. backpressure
  // from the conditioner. The conditioner will still use the amount of bits configured in
  // HEALTH_TEST_WINDOW.FIPS_WINDOW to produce the seed, and the produced seed is okay to use.
  // But as the dropped bits are still tested, the effective test window increases beyond the
  // value configured in HEALTH_TEST_WINDOW.FIPS_WINDOW.
  //
  // Signaling this condition serves the following purposes:
  // 1. When running in Firmware Override: Observe mode, dropping post-health test entropy bits
  //    may cause the entropy bits observed from the Observe FIFO to be non-contiguous, causing
  //    the observed bits to be not usable for validation purposes. Note that Firmware Override:
  //    Extract & Insert mode is not affected by this.
  // 2. It allows the DV environment to know when entropy bits have been dropped which simplifies
  //    DV.
  // 3. It helps tuning the depth of the distr FIFO which can be used to absorb the backpressure
  //    of the conditioner.

  // The pop signal of the preceeding esrng FIFO is unconditional, meaning samples are dropped
  // whenever the esbit or postht FIFO is full in single-channel or multi-channel mode,
  // respectively.
  assign postht_entropy_drop_alert = sfifo_esrng_not_empty &&
      (rng_bit_en ? !pfifo_esbit_not_full : !pfifo_postht_not_full);

  assign hw2reg.recov_alert_sts.postht_entropy_drop_alert.de = postht_entropy_drop_alert;
  assign hw2reg.recov_alert_sts.postht_entropy_drop_alert.d  = postht_entropy_drop_alert;

  //--------------------------------------------------------------
  // Pack health tested esrng bus into single bit packer FIFO.
  //--------------------------------------------------------------

  // SEC_CM: CONFIG.MUBI
  assign mubi_rng_bit_en = mubi4_t'(reg2hw.conf.rng_bit_enable.q);
  assign rng_bit_enable_pfe = mubi4_test_true_strict(mubi_rng_bit_en_fanout[0]);
  assign rng_bit_enable_pfa = mubi4_test_invalid(mubi_rng_bit_en_fanout[1]);
  assign hw2reg.recov_alert_sts.rng_bit_enable_field_alert.de = rng_bit_enable_pfa;
  assign hw2reg.recov_alert_sts.rng_bit_enable_field_alert.d  = rng_bit_enable_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_rng_bit_en (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_rng_bit_en),
    .mubi_o(mubi_rng_bit_en_fanout)
  );


  assign rng_bit_en = rng_bit_enable_pfe;
  assign rng_bit_sel = reg2hw.conf.rng_bit_sel.q;

  prim_packer_fifo #(
    .InW(1),
    .OutW(RngBusWidth),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_esbit (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (pfifo_esbit_clr),
    .wvalid_i   (pfifo_esbit_push),
    .wdata_i    (pfifo_esbit_wdata),
    .wready_o   (pfifo_esbit_not_full),
    .rvalid_o   (pfifo_esbit_not_empty),
    .rdata_o    (pfifo_esbit_rdata),
    .rready_i   (pfifo_esbit_pop),
    .depth_o    ()
  );

  // The prim_packer_fifo primitive is constructed to only accept pushes if there is indeed space
  // available. The pop signal of the preceeding esrng FIFO is unconditional, meaning samples can
  // be dropped before the esbit FIFO in case of backpressure. The samples are however still
  // tested.
  assign pfifo_esbit_push = rng_bit_en && sfifo_esrng_not_empty;
  assign pfifo_esbit_clr = ~es_delayed_enable;
  assign pfifo_esbit_pop = rng_bit_en && pfifo_esbit_not_empty && pfifo_postht_not_full;
  assign pfifo_esbit_wdata =
         (rng_bit_sel == 2'h0) ? sfifo_esrng_rdata[0] :
         (rng_bit_sel == 2'h1) ? sfifo_esrng_rdata[1] :
         (rng_bit_sel == 2'h2) ? sfifo_esrng_rdata[2] :
         sfifo_esrng_rdata[3];


  //--------------------------------------------
  // pack tested entropy into 32 bit packer
  //--------------------------------------------

  prim_packer_fifo #(
    .InW(RngBusWidth),
    .OutW(PostHTWidth),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_postht (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (pfifo_postht_clr),
    .wvalid_i   (pfifo_postht_push),
    .wdata_i    (pfifo_postht_wdata),
    .wready_o   (pfifo_postht_not_full),
    .rvalid_o   (pfifo_postht_not_empty),
    .rdata_o    (pfifo_postht_rdata),
    .rready_i   (pfifo_postht_pop),
    .depth_o    ()
  );

  // The prim_packer_fifo primitive is constructed to only accept pushes if there is indeed space
  // available. In case the single-bit mode is enabled, the pop signal of the preceeding esbit FIFO
  // is conditional on the full status of the postht FIFO, meaning backpressure can be handled. In
  // case the single-bit mode is disabled, the pop signal of the preceeding esrng FIFO is
  // unconditional, meaning samples can be dropped before the esbit in case of backpressure. The
  // samples are however still tested.
  assign pfifo_postht_push = rng_bit_en ? pfifo_esbit_not_empty : sfifo_esrng_not_empty;

  assign pfifo_postht_wdata = rng_bit_en ? pfifo_esbit_rdata :
                              sfifo_esrng_rdata;

  // For verification purposes, let post-disable data continue through to the SHA engine if it has
  // made it past the health checks, when in standard (non-fw_ov) mode.  This allows scoreboards
  // to use the same data set for computing both the SHA engine outputs and the health-check stats.
  //
  // In fw_ov mode it is preferable (from a verification standpoint) to clear all FIFOs whenever
  // disabled. Given the lack of handshaking on the fw_ov register path, this is easier to predict.
  // Also, there is no association between SHA data and health test windows in FW_OV mode, so there
  // is no benefit in this mode to clearing the SHA FIFOs at the same time we clear the HT
  // statistics.
  assign pfifo_postht_clr = fw_ov_mode_entropy_insert ? !es_enable_fo[7] : !es_delayed_enable;

  // Pop whenever the distribution FIFO is not full. The distribution FIFO can be sized such that
  // it's never going to be full even under pessimistic operating conditions.
  assign pfifo_postht_pop = sfifo_distr_push & sfifo_distr_not_full;

  //--------------------------------------------
  // buffer entropy in ditribution FIFO
  //--------------------------------------------

  // The purpose of this FIFO is to buffer postht entropy bits in case the conditioner cannot
  // accept them at the moment, i.e., because it's busy or because it's waiting on the CS AES halt
  // interface before it can run. By properly sizing this FIFO, it can be guaranteed that even
  // under pessimistic operating conditions (see entropy_src_rng_max_rate test), entropy bits never
  // need to be dropped from the hardware pipeline.

  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(DistrFifoWidth),
    .Pass(1),
    .Depth(DistrFifoDepth),
    .OutputZeroIfEmpty(0),
    .Secure(1)
  ) u_prim_fifo_sync_distr (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (sfifo_distr_clr),
    .wvalid_i   (sfifo_distr_push),
    .wdata_i    (sfifo_distr_wdata),
    .wready_o   (sfifo_distr_not_full),
    .rvalid_o   (sfifo_distr_not_empty),
    .rdata_o    (sfifo_distr_rdata),
    .rready_i   (sfifo_distr_pop),
    .full_o     (sfifo_distr_full),
    .depth_o    (),
    .err_o      (sfifo_distr_int_err)
  );

  // The prim_fifo_sync primitive is constructed to only accept pushes if there is indeed space
  // available. Backpressure is handled at the sender.
  assign sfifo_distr_push = pfifo_postht_not_empty;
  assign sfifo_distr_wdata = pfifo_postht_rdata;

  assign sfifo_distr_clr = fw_ov_mode_entropy_insert ? !es_enable_fo[19] : !es_delayed_enable;

  // In firmware override mode with extract & insert enabled, post-health test entropy bits can
  // only move into the observe FIFO. Once the observe FIFO is full, post-health test entropy is
  // just discarded.
  assign sfifo_distr_pop = fw_ov_mode_entropy_insert ? sfifo_distr_not_empty :
                           // In firmware override mode (observe only) or during normal
                           // operation, post-health test entropy bits continue to flow
                           // through the hardware pipeline.
                           es_bypass_mode ? pfifo_bypass_push :
                           pfifo_precon_push & pfifo_precon_not_full;

  // fifo err
  // Note that for the used prim_fifo_sync and prim_packer_fifo primitives it is not an error to
  // push to a FIFO that is full. The primitives simply don't accept the data when full. The
  // backpressure needs to be handled at the sender.
  assign sfifo_distr_err =
         {1'b0,
         (sfifo_distr_pop && !sfifo_distr_not_empty),
         (sfifo_distr_full && !sfifo_distr_not_empty) || sfifo_distr_int_err};

  //--------------------------------------------
  // store entropy into a 32 entry deep FIFO
  //--------------------------------------------

  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(ObserveFifoWidth),
    .Pass(0),
    .Depth(ObserveFifoDepth),
    .OutputZeroIfEmpty(1), // Prevent SVA from firing due unknown module outputs.
    .Secure(1)
  ) u_prim_fifo_sync_observe (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (sfifo_observe_clr),
    .wvalid_i   (sfifo_observe_push),
    .wdata_i    (sfifo_observe_wdata),
    .wready_o   (),
    .rvalid_o   (sfifo_observe_not_empty),
    .rdata_o    (sfifo_observe_rdata),
    .rready_i   (sfifo_observe_pop),
    .full_o     (sfifo_observe_full),
    .depth_o    (sfifo_observe_depth),
    .err_o      (sfifo_observe_int_err)
  );

  // The Observe fifo is intended to hold kilobits of contiguous data, yet still gracefully
  // drop data when full.  This flop gates the observe fifo. If it ever overflows, no new data is
  // allowed until it is empty.  Thus if the rate of CSR uptake almost matches the RNG data rate
  // the FIFO avoids unnecessary segmentation, and guarantees that the remaining RNG data is as
  // contiguous as possible.
  logic sfifo_observe_gate_d, sfifo_observe_gate_q;

  assign sfifo_observe_gate_d = (sfifo_distr_pop && sfifo_observe_full) ? 1'b0 :
                                !sfifo_observe_not_empty                ? 1'b1 :
                                sfifo_observe_gate_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sfifo_observe_gate_q <= 1'b1;
    end else begin
      sfifo_observe_gate_q <= sfifo_observe_gate_d;
    end
  end

  assign hw2reg.fw_ov_rd_fifo_overflow.d  = !sfifo_observe_gate_d;
  assign hw2reg.fw_ov_rd_fifo_overflow.de = 1'b1;

  assign observe_fifo_thresh_met = fw_ov_mode && (observe_fifo_thresh != '0) &&
         (observe_fifo_thresh <= sfifo_observe_depth) && es_enable_fo[8];

  assign hw2reg.observe_fifo_depth.d = sfifo_observe_depth;

  // fifo controls
  assign sfifo_observe_push = fw_ov_mode && sfifo_distr_pop &&
                              (sfifo_observe_gate_q || !sfifo_observe_not_empty);

  assign sfifo_observe_clr  = ~es_enable_fo[9];

  assign sfifo_observe_wdata = sfifo_distr_rdata;

  assign sfifo_observe_pop =
         (fw_ov_mode && fw_ov_fifo_rd_pulse);

  // fifo err
  // Note that for the used prim_fifo_sync and prim_packer_fifo primitives it is not an error to
  // push to a FIFO that is full. The primitives simply don't accept the data when full. The
  // backpressure needs to be handled at the sender.
  assign sfifo_observe_err =
         {1'b0,
         (sfifo_observe_pop && !sfifo_observe_not_empty),
         (sfifo_observe_full && !sfifo_observe_not_empty) || sfifo_observe_int_err};


  //--------------------------------------------
  // pack entropy into 64 bit packer
  //--------------------------------------------

  prim_packer_fifo #(
    .InW(ObserveFifoWidth),
    .OutW(PreCondWidth),
    .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_precon (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (pfifo_precon_clr),
    .wvalid_i   (pfifo_precon_push),
    .wdata_i    (pfifo_precon_wdata),
    .wready_o   (pfifo_precon_not_full),
    .rvalid_o   (pfifo_precon_not_empty),
    .rdata_o    (pfifo_precon_rdata),
    .rready_i   (pfifo_precon_pop),
    .depth_o    ()
  );

  // When bypassing the hardware conditioning - due to a) disabling FIPS mode or b) routing entropy
  // to the ENTROPY_DATA register (ES_ROUTE) and bypassing the conditioner (ES_TYPE) - nothing is
  // going into the conditioner.
  assign pfifo_precon_push = es_bypass_mode ? 1'b0 :
                             // In firmware override mode with extract & insert enabled, only bits
                             // inserted by firmware continue down the pipeline.
                             fw_ov_mode_entropy_insert ? fw_ov_fifo_wr_pulse :
                             // Otherwise post-health test entropy bits continue to flow
                             // downstream. This includes observe-only firmware override mode.
                             sfifo_distr_not_empty;

  assign pfifo_precon_wdata = fw_ov_mode_entropy_insert ? fw_ov_wr_data :
                              sfifo_distr_rdata;

  // For verification purposes, let post-disable data continue through to the SHA engine if it has
  // made it past the health checks, when in standard (non-fw_ov) mode.  This allows scoreboards
  // to use the same data set for computing both the SHA engine outputs and the health-check stats.
  //
  // In fw_ov mode it is preferable (from a verification standpoint) to clear all FIFOs whenever
  // disabled. Given the lack of handshaking on the fw_ov register path, this is easier to predict.
  // Also, there is no association between SHA data and health test windows in FW_OV mode, so there
  // is no benefit in this mode to clearing the SHA FIFOs at the same time we clear the HT
  // statistics.
  //
  // Corner case: Even in FW_OV mode, if a full SHA word is ready as the disable comes in,
  // let it stay in the FIFO until the SHA engine has picked it up, as verification has no way
  // of knowing if a word will get stalled by SHA backpressure.  This is not a problem however
  // as the reset is only important for clearing 32-bit half-SHA-words.
  assign pfifo_precon_clr = fw_ov_mode_entropy_insert ?
                            ~es_enable_fo[10] & ~pfifo_precon_not_empty :
                            ~es_delayed_enable & ~pfifo_precon_not_empty;

  assign pfifo_precon_pop = (pfifo_cond_push && sha3_msgfifo_ready);

  assign es_fw_ov_wr_alert = fw_ov_mode && fw_ov_mode_entropy_insert &&
         fw_ov_fifo_wr_pulse && fw_ov_wr_fifo_full;

  assign es_fw_ov_disable_alert = fw_ov_mode && fw_ov_mode_entropy_insert &&
         !es_bypass_mode && fw_ov_sha3_disable_pulse && fw_ov_wr_fifo_full;

  //--------------------------------------------
  // entropy conditioner
  //--------------------------------------------
  // This block takes in either post-health test entropy bits (when running in FIPS/CC compliant
  // mode) or entropy injected by software (when running in Firmware Override: Extract & Insert
  // mode).
  // The amount of entropy consumed to generate a 384-bit seed depends on the mode of operation:
  // - In FIPS/CC compliant mode, HEALTH_TEST_WINDOWS.FIPS_WINDOW x 4 bits (by default 2048 bits)
  //   are required to produce one 384-bit seed. For the first seed after start up, the number of
  //   bits consumed is doubled to align with the required 1024 samples of 4 bits for startup
  //   health testing.
  //   For windows which fail a health test, the entropy is still absorbed by the SHA3 engine
  //   but no seed is produced. In order for the SHA3 engine to produce a seed, the last window it
  //   absorbed must have passed the health tests.
  // - In Firmware Override: Extract & Insert mode, the operation of the SHA3 engine is software
  //   defined.
  //
  // Note that the final absorption operation of the SHA3 engine is triggered by the main state
  // machine (upon receiving the health-test done pulse). The SHA3 engine is also triggered
  // internally by the padding logic whenever 832 bits (= the rate or block size of SHA3-384) have
  // been received.
  //
  // Note on backpressure handling from the SHA3 engine:
  // To avoid inferring a combo loop, the msg_valid_i input (pfifo_cond_push signal) must not
  // depend on the msg_ready_o output (sha3_msgfifo_ready). However, we can always push into the
  // SHA3 engine as long as the precon FIFO contains valid data. The ready output is just used to
  // determine when to pop from the precon FIFO.

  assign pfifo_cond_push  = pfifo_precon_not_empty && !es_bypass_mode;
  assign pfifo_cond_wdata = pfifo_precon_rdata;

  assign msg_data[0] = pfifo_cond_wdata;

  assign pfifo_cond_rdata = sha3_state[0][SeedLen-1:0];

  // SHA3 hashing engine
  sha3 #(
    .EnMasking (Sha3EnMasking)
  ) u_sha3 (
    .clk_i,
    .rst_ni,

    // MSG_FIFO interface
    .msg_valid_i (pfifo_cond_push),
    .msg_data_i  (msg_data),
    .msg_strb_i  ({8{pfifo_cond_push}}),
    .msg_ready_o (sha3_msgfifo_ready),

    // Entropy interface - not using
    .rand_valid_i    (1'b0),
    .rand_early_i    (1'b0),
    .rand_data_i     ('0),
    .rand_aux_i      ('0),
    .rand_update_o   (),
    .rand_consumed_o (),

    // N, S: Used in cSHAKE mode
    .ns_data_i       ('0), // ns_prefix),

    // Configurations
    .mode_i     (sha3_pkg::Sha3), // Use SHA3 mode
    .strength_i (sha3_pkg::L384), // Use keccak_strength_e of L384

    // Controls (CMD register)
    .start_i    (sha3_start       ),
    .process_i  (sha3_process     ),
    .run_i      (1'b0             ), // For software application
    .done_i     (sha3_done        ),

    // LC escalation
    .lc_escalate_en_i (lc_ctrl_pkg::Off),

    .absorbed_o (sha3_absorbed),
    .squeezing_o (sha3_squeezing),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (sha3_state_vld),
    .state_o       (sha3_state),

    // REQ/ACK interface to avoid power spikes
    .run_req_o(cs_aes_halt_req),
    .run_ack_i(cs_aes_halt_i.cs_aes_halt_ack),

    .error_o (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o  (sha3_count_error),
    .keccak_storage_rst_error_o (sha3_rst_storage_err)
  );

  //--------------------------------------------
  // bypass SHA conditioner path
  //--------------------------------------------

  prim_packer_fifo #(
     .InW(PostHTWidth),
     .OutW(SeedLen),
     .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_bypass (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (pfifo_bypass_clr),
    .wvalid_i   (pfifo_bypass_push),
    .wdata_i    (pfifo_bypass_wdata),
    .wready_o   (pfifo_bypass_not_full),
    .rvalid_o   (pfifo_bypass_not_empty),
    .rdata_o    (pfifo_bypass_rdata),
    .rready_i   (pfifo_bypass_pop),
    .depth_o    ()
  );

  // Unless the hardware conditioning is bypassed - due to a) disabling FIPS mode or b) routing
  // entropy to the ENTROPY_DATA register (ES_ROUTE) and bypassing the conditioner (ES_TYPE) -
  // nothing is going into the bypass FIFO.
  assign pfifo_bypass_push = !es_bypass_mode ? 1'b0 :
                             // In firmware override mode with extract & insert enabled, only bits
                             // inserted by firmware continue down the pipeline
                             fw_ov_mode_entropy_insert ? fw_ov_fifo_wr_pulse :
                             // Otherwise post-health test entropy bits continue to flow
                             // downstream. This includes observe-only firmware override mode.
                             sfifo_distr_not_empty;

  assign pfifo_bypass_wdata = fw_ov_mode_entropy_insert ? fw_ov_wr_data :
                              sfifo_distr_rdata;

  assign pfifo_bypass_clr = !es_enable_fo[11];

  // Corner case: If the main state machine encounters an alert, drain the
  // bypass fifo, to get rid of the seeds and let the HT stats continue.
  assign pfifo_bypass_pop =
         fw_ov_mode_entropy_insert ? pfifo_bypass_not_empty :
         bypass_stage_pop;

  // mux to select between fips and bypass mode
  assign final_es_data = es_bypass_mode ? pfifo_bypass_rdata : pfifo_cond_rdata;


  //--------------------------------------------
  // state machine to coordinate fifo flow
  //--------------------------------------------
  assign main_sm_done_pulse = rng_bit_en ? ht_done_pulse_qq : ht_done_pulse_q;
  assign main_sm_ht_failed  = rng_bit_en ? ht_failed_qq : ht_failed_q;

  // SEC_CM: CTR.LOCAL_ESC
  // SEC_CM: MAIN_SM.FSM.SPARSE
  entropy_src_main_sm
    u_entropy_src_main_sm (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),
    .enable_i             (main_sm_enable),
    .fw_ov_ent_insert_i   (fw_ov_mode_entropy_insert),
    .fw_ov_sha3_start_i   (fw_ov_sha3_start_pfe),
    .ht_done_pulse_i      (main_sm_done_pulse),
    .ht_fail_pulse_i      (main_sm_ht_failed),
    .alert_thresh_fail_i  (alert_threshold_fail),
    .rst_alert_cntr_o     (rst_alert_cntr),
    .bypass_mode_i        (es_bypass_mode),
    .bypass_stage_rdy_i   (pfifo_bypass_not_empty),
    .sha3_state_vld_i     (sha3_state_vld),
    .main_stage_push_o    (main_stage_push_raw),
    .bypass_stage_pop_o   (bypass_stage_pop),
    .boot_phase_done_o    (boot_phase_done),
    .sha3_start_o         (sha3_start_raw),
    .sha3_process_o       (sha3_process),
    .sha3_done_o          (sha3_done),
    .local_escalate_i     (fatal_loc_events),
    .main_sm_alert_o      (es_main_sm_alert),
    .main_sm_idle_o       (es_main_sm_idle),
    .main_sm_state_o      (es_main_sm_state),
    .main_sm_err_o        (es_main_sm_err)
  );

  // es to cs halt request to reduce power spikes
  assign cs_aes_halt_d = cs_aes_halt_req;
  assign cs_aes_halt_o.cs_aes_halt_req = cs_aes_halt_q;

  //--------------------------------------------
  // Corner case masking of main_sm inputs/outputs
  //--------------------------------------------

  // When operating in RNG mode the state machine does not respond
  // immediately to disable requests if it processing the SHA output
  // (here indicated by the cs_aes_halt_req handshake).  The SHA engine
  // will continue to process even if the module is disabled.  These seeds
  // that continue to process after the disable signal are referred to as
  // stale.
  //
  // If the SHA processing were instantaneous, stale seeds would be discarded
  // when the esfinal fifo was cleard on diable.  Though since processing
  // can push through a disable pulse, stale seeds need to be identified,
  // and held back from the esfinal FIFO.
  //
  // There is at most one seed processing at a time so, we simply need to
  // detect when a stale seed has commenced processing, and mask the following
  // main_stage_push signal.

  assign stale_seed_processing = ~es_bypass_mode & ~fw_ov_mode_entropy_insert &
                                 cs_aes_halt_req & ~es_enable_fo[12];
  assign sha3_flush_d = stale_seed_processing ? 1'b1 :
                        main_stage_push_raw ? 1'b0 :
                        sha3_flush_q;

  // If the user incorrectly disables the fw_ov SHA3 processing while
  // data is in the pipeline, it can potentially scramble two outputs.
  // Thus in addition to triggering a recoverable alert, we mark the
  // following _two_ outputs as corrupted and to not let them in the
  // esfinal FIFO
  assign fw_ov_corrupted_d = es_fw_ov_disable_alert ? 2'b11 :
                             !es_bypass_mode && main_stage_push_raw ? {1'b0, fw_ov_corrupted_q[1]} :
                             fw_ov_corrupted_q;

  assign fw_ov_corrupted = (|fw_ov_corrupted_q) & !es_bypass_mode;


  assign main_stage_push = main_stage_push_raw & !sha3_flush_q & !fw_ov_corrupted;

  // Use the delayed enable signal to keep the Main SM enabled while Data is in flight, and
  // to make sure it receives a delayed disable pulse after finishing any final SHA processing
  // commands
  assign main_sm_enable = es_delayed_enable;

  // The main SM can also generate redundant start pulses. After data can be pushed into SHA,
  // the SM can be disabled leaving entropy in the SHA sponge.  This is fine, but the SM will
  // have no recollection of this previous start pulse.  We track redundant start pulses
  // outside the SM and suppress them as needed.
  assign sha3_start_mask_d = sha3_start_raw ? 1'b1 :
                             sha3_process   ? 1'b0 :
                             sha3_start_mask_q;
  assign sha3_start = sha3_start_raw & ~sha3_start_mask_q;

  //--------------------------------------------
  // send processed entropy to final fifo
  //--------------------------------------------

  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(1+SeedLen),
    .Pass(0),
    .Depth(EsFifoDepth),
    .OutputZeroIfEmpty(0),
    .Secure(1)
  ) u_prim_fifo_sync_esfinal (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (sfifo_esfinal_clr),
    .wvalid_i       (sfifo_esfinal_push),
    .wready_o       (sfifo_esfinal_not_full),
    .wdata_i        (sfifo_esfinal_wdata),
    .rvalid_o       (sfifo_esfinal_not_empty),
    .rready_i       (sfifo_esfinal_pop),
    .rdata_o        (sfifo_esfinal_rdata),
    .full_o         (sfifo_esfinal_full),
    .depth_o        (sfifo_esfinal_depth),
    .err_o          (sfifo_esfinal_int_err)
  );

  // The FIPS flag is fully determined in SW. This has to be the case since we don't know
  // which mode of operation will be validated/certified. Another reason is that SW can
  // set the threshold values arbitrarily, which on its own makes the FIPS bit basically
  // SW defined.
  assign fips_compliance = es_enable_fo[13] && fips_flag_pfe;

  // fifo controls
  // No backpressure is possible at this point. If the esfinal FIFO is already full and a new seed
  // is pushed, the push is ignored and the seed is lost.
  assign sfifo_esfinal_push =
         fw_ov_mode_entropy_insert && es_bypass_mode ? pfifo_bypass_not_empty :
         main_stage_push;

  assign sfifo_esfinal_clr  = !es_enable_fo[14];
  assign sfifo_esfinal_wdata = {fips_compliance,final_es_data};
  assign sfifo_esfinal_pop = es_route_to_sw ? swread_done : es_hw_if_fifo_pop;
  assign {esfinal_fips_flag,esfinal_data} = sfifo_esfinal_rdata;

  // fifo err
  // Note that for the used prim_fifo_sync and prim_packer_fifo primitives it is not an error to
  // push to a FIFO that is full. The primitives simply don't accept the data when full. The
  // backpressure needs to be handled at the sender.
  assign sfifo_esfinal_err =
         {1'b0,
          (sfifo_esfinal_pop && !sfifo_esfinal_not_empty),
          (sfifo_esfinal_full && !sfifo_esfinal_not_empty) || sfifo_esfinal_int_err};

  // drive out hw interface
  assign es_hw_if_req = entropy_src_hw_if_i.es_req;
  assign entropy_src_hw_if_o.es_ack = es_hw_if_ack;
  assign entropy_src_hw_if_o.es_bits = esfinal_data;
  assign entropy_src_hw_if_o.es_fips = esfinal_fips_flag;

  // SEC_CM: ACK_SM.FSM.SPARSE
  entropy_src_ack_sm u_entropy_src_ack_sm (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .enable_i         (es_enable_fo[15]),
    .req_i            (es_hw_if_req),
    .ack_o            (es_hw_if_ack),
    .fifo_not_empty_i (sfifo_esfinal_not_empty && !es_route_to_sw),
    .local_escalate_i (es_cntr_err),
    .fifo_pop_o       (es_hw_if_fifo_pop),
    .ack_sm_err_o     (es_ack_sm_err)
  );

  //--------------------------------------------
  // data path integrity check
  // - a countermeasure to detect entropy bus tampering attempts
  // - checks to make sure repeated data sets off
  //   an alert for sw to handle
  //--------------------------------------------

  // SEC_CM: ESFINAL_RDATA.BUS.CONSISTENCY

  // capture a copy of the entropy data
  assign es_rdata_capt_vld = (sfifo_esfinal_pop && sfifo_esfinal_not_empty);

  assign es_rdata_capt_d = es_rdata_capt_vld ? sfifo_esfinal_rdata[63:0] : es_rdata_capt_q;

  assign es_rdata_capt_vld_d =
         !es_enable_fo[16] ? 1'b0 :
         es_rdata_capt_vld ? 1'b1 :
         es_rdata_capt_vld_q;

  // continuous compare of the entropy data
  assign es_bus_cmp_alert = es_rdata_capt_vld && es_rdata_capt_vld_q &&
         (es_rdata_capt_q == sfifo_esfinal_rdata[63:0]);


  //----------------------------------------------------
  // software es read path via ENTROPY_DATA register
  //----------------------------------------------------

  // Sync and evaluate the OTP input.
  prim_mubi8_sync #(
    .NumCopies(1),
    .AsyncOn(1)
  ) u_prim_mubi8_sync_es_fw_read (
    .clk_i,
    .rst_ni,
    .mubi_i(otp_en_entropy_src_fw_read_i),
    .mubi_o({en_entropy_src_fw_read})
  );
  assign efuse_es_sw_reg_en = prim_mubi_pkg::mubi8_test_true_strict(en_entropy_src_fw_read);

  // Is the ENTROPY_DATA register readable?
  assign es_data_reg_rd_en = es_enable_fo[17] && efuse_es_sw_reg_en && entropy_data_reg_en_pfe;

  // Interface the esfinal FIFO and cut its 384-bit output into 32-bit chunks for software.
  // We're done after the last read.
  assign swread_done = reg2hw.entropy_data.re && (swread_idx_q == LastSwRead[SwReadIdxWidth-1:0]);

  // Increment the index counter upon reads from software.
  assign swread_idx_incr = reg2hw.entropy_data.re;

  // Unless the ENTROPY_DATA CSR is readable, keep clearing the index counter. Clear the counter
  // after a full seed has been read.
  assign swread_idx_clr = !es_data_reg_rd_en || swread_done;

  // Index counter
  assign swread_idx_d = !es_enable_fo[18] ? '0                  :
                        swread_idx_clr    ? '0                  :
                        swread_idx_incr   ? swread_idx_q + 1'b1 : swread_idx_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : swread_idx_reg
    if (!rst_ni) begin
      swread_idx_q <= '0;
    end else begin
      swread_idx_q <= swread_idx_d;
    end
  end

  // Forward the relevant part of the valid esfinal output or 0 if ES_ROUTE is off.
  assign swread_data = sfifo_esfinal_not_empty && es_route_to_sw ?
      esfinal_data[swread_idx_q * FullRegWidth +: FullRegWidth] : '0;

  // This primitive is used to place a size-only constraint on the buffers to act as a synthesis
  // optimization barrier. This ensures ES_ROUTE and ENTROPY_DATA_REG_ENABLE together with the OTP
  // input are taken into account in separately.
  prim_buf #(
    .Width(FullRegWidth)
  ) u_prim_buf_swread_data (
    .in_i (swread_data),
    .out_o(swread_data_buf)
  );

  // Forward the data to the ENTROPY_DATA CSR or 0 if the CSR is not readable.
  assign hw2reg.entropy_data.d = es_data_reg_rd_en ? swread_data_buf : '0;


  //--------------------------------------------
  // unused signals
  //--------------------------------------------

  assign unused_err_code_test_bit = (|{err_code_test_bit[27:25],err_code_test_bit[19:4]});
  assign unused_sha3_state = (|sha3_state[0][sha3_pkg::StateW-1:SeedLen]);
  assign unused_entropy_data = (|reg2hw.entropy_data.q);
  assign unused_fw_ov_rd_data = (|reg2hw.fw_ov_rd_data.q);
  assign unused_sfifo_esrng_not_full = sfifo_esrng_not_full;
  assign unused_sfifo_esfinal_not_full = sfifo_esfinal_not_full;

  //--------------------------------------------
  // Assertions
  //--------------------------------------------
`ifdef INC_ASSERT
`include "prim_macros.svh"

  // Count number of disables since last reset.
  logic [63:0] disable_cnt_d, disable_cnt_q;
  always_comb begin
    disable_cnt_d = disable_cnt_q;
    if (!mubi4_test_true_strict(mubi_mod_en_dly_d) &&
        mubi4_test_true_strict(mubi_mod_en_dly_q)) begin
      disable_cnt_d += 1;
    end
  end

  // Assert that no entropy gets dropped during FIPS-compliant operation mode.
  //
  // The following code, which includes counters, small FSMs, and assertions, tracks entropy bits
  // from the noise source input through Entropy Source to the hardware interface output and checks
  // that in FIPS-compliant mode entropy does not get dropped unless it should get dropped.  The
  // code is arranged in the same order as entropy flows through Entropy Source, so having Entropy
  // Source's block diagram ready when reading this code is highly recommended.

  // Delay `es_delayed_enable` by one clock cycle to track when Entropy Source actually accepts RNG
  // inputs.
  logic es_delayed_enable_d, es_delayed_enable_q;
  assign es_delayed_enable_d = es_delayed_enable;

  // Count number of valid bits from RNG input (RNG_BUS_WIDTH wide) while Entropy Source is enabled.
  logic [63:0] rng_valid_bit_cnt_d, rng_valid_bit_cnt_q;
  assign rng_valid_bit_cnt_d = entropy_src_rng_i.rng_valid && es_delayed_enable_q ?
                               rng_valid_bit_cnt_q + RNG_BUS_WIDTH :
                               rng_valid_bit_cnt_q;

  // Count number of bits pushed into esrng FIFO (RngBusWidth wide).
  logic [63:0] esrng_push_bit_cnt_d, esrng_push_bit_cnt_q;
  assign esrng_push_bit_cnt_d = sfifo_esrng_push & sfifo_esrng_not_full ?
                                esrng_push_bit_cnt_q + RngBusWidth :
                                esrng_push_bit_cnt_q;

  // Assert that as many bits got pushed into the esrng FIFO (destination) as there were valid RNG
  // input bits (source).  RngBusWidth bits may get lost after every re-enable; add a margin to
  // account for that.
  `ASSERT_AT_RESET_AND_FINAL(ValidRngBitsPushedIntoEsrngFifo_A,
                             `WITHIN_MARGIN(esrng_push_bit_cnt_q,        // actual
                                            rng_valid_bit_cnt_q,         // expected
                                            disable_cnt_q * RngBusWidth, // allowed less
                                            0))                          // allowed more

  // Count number of bits pushed into esbit FIFO (1 wide input, RngBusWidth wide output).
  logic [63:0] esbit_push_bit_cnt_d, esbit_push_bit_cnt_q;
  assign esbit_push_bit_cnt_d = pfifo_esbit_push & pfifo_esbit_not_full ?
                                esbit_push_bit_cnt_q + 1 :
                                esbit_push_bit_cnt_q;

  // Count number of bits pushed into postht FIFO (RngBusWidth wide input, PostHTWidth wide output).
  logic [63:0] postht_push_bit_cnt_d, postht_push_bit_cnt_q;
  assign postht_push_bit_cnt_d = pfifo_postht_push & pfifo_postht_not_full ?
                                 postht_push_bit_cnt_q + RngBusWidth :
                                 postht_push_bit_cnt_q;

  // Count number of bits pushed into postht FIFO from esrng FIFO.
  logic [63:0] postht_from_esrng_push_bit_cnt_d, postht_from_esrng_push_bit_cnt_q;
  assign postht_from_esrng_push_bit_cnt_d =
      pfifo_postht_push & pfifo_postht_not_full & ~rng_bit_en ?
      postht_from_esrng_push_bit_cnt_q + RngBusWidth :
      postht_from_esrng_push_bit_cnt_q;

  // Assert that as many bits got pushed into the esbit FIFO or the postht FIFO (destinations) as
  // into the esrng FIFO (source).  The number of bits pushed into the esbit FIFO has to be
  // multiplied by the output width of the esrng FIFO (RngBusWidth) because only 1 bit gets pushed
  // into the esbit FIFO for every pop from the esrng FIFO.  Add a margin (allowed less) because:
  // - RngBusWidth bits may get lost after every re-enable
  // - one entry may just have been pushed into esrng FIFO when the assertion gets evaluated.
  `ASSERT_AT_RESET_AND_FINAL(EsrngFifoPushedIntoEsbitOrPosthtFifos_A,
                             `WITHIN_MARGIN((esbit_push_bit_cnt_q * RngBusWidth +
                                             postht_from_esrng_push_bit_cnt_q), // actual
                                            esrng_push_bit_cnt_q,               // expected
                                            (disable_cnt_q + 1) * RngBusWidth,  // allowed less
                                            0))                                 // allowed more

  // Count number of bits pushed into postht FIFO from esbit FIFO.
  logic [63:0] postht_from_esbit_push_bit_cnt_d, postht_from_esbit_push_bit_cnt_q;
  assign postht_from_esbit_push_bit_cnt_d =
      pfifo_postht_push & pfifo_postht_not_full & rng_bit_en ?
      postht_from_esbit_push_bit_cnt_q + RngBusWidth :
      postht_from_esbit_push_bit_cnt_q;

  // Assert that as many bits got pushed into the postht FIFO (destination) as into the esbit FIFO
  // (source) when the latter was selected as source.  Add a margin (allowed less) because:
  // - RngBusWidth bits may get lost after every re-enable
  // - esbit FIFO may be partially full when the assertion gets evaluated.
  `ASSERT_AT_RESET_AND_FINAL(EsbitFifoPushedIntoPosthtFifo_A,
                             `WITHIN_MARGIN(postht_from_esbit_push_bit_cnt_q,      // actual
                                            esbit_push_bit_cnt_q,                  // expected
                                            (disable_cnt_q + 1) * RngBusWidth - 1, // allowed less
                                            0))                                    // allowed more

  // Assert that as many bits got pushed into the postht FIFO as got counted from the esrng FIFO or
  // the esbit FIFO.  This assertion checks more the completeness of the other assertions than the
  // design itself.
  `ASSERT_AT_RESET_AND_FINAL(PosthtFifoPushedFromEsbitOrEsrngFifos_A,
                             postht_push_bit_cnt_q == (postht_from_esrng_push_bit_cnt_q +
                                                       postht_from_esbit_push_bit_cnt_q))

  // Count number of bits popped from postht FIFO (PostHTWidth wide output) when bypass mode was
  // disabled.
  logic [63:0] postht_non_bypass_pop_bit_cnt_d, postht_non_bypass_pop_bit_cnt_q;
  assign postht_non_bypass_pop_bit_cnt_d =
      pfifo_postht_pop & pfifo_postht_not_empty & ~es_bypass_mode ?
      postht_non_bypass_pop_bit_cnt_q + PostHTWidth :
      postht_non_bypass_pop_bit_cnt_q;

  // Count number of bits pushed into distr FIFO (DistrFifoWidth wide input and output).
  logic [63:0] distr_non_bypass_push_bit_cnt_d, distr_non_bypass_push_bit_cnt_q;
  assign distr_non_bypass_push_bit_cnt_d =
      sfifo_distr_push & sfifo_distr_not_full & ~es_bypass_mode ?
      distr_non_bypass_push_bit_cnt_q + DistrFifoWidth :
      distr_non_bypass_push_bit_cnt_q;

  // Assert that as many bits got pushed into the distr FIFO (destination) as got popped from the
  // postht FIFO when bypass mode was disabled (source).
  `ASSERT_AT_RESET_AND_FINAL(PosthtFifoPushedIntoDistrFifo_A,
                             distr_non_bypass_push_bit_cnt_q == postht_non_bypass_pop_bit_cnt_q)

  // Count number of bits popped from distr FIFO (DistrFifoWidth wide output) when bypass mode was
  // disabled.
  logic [63:0] distr_non_bypass_pop_bit_cnt_d, distr_non_bypass_pop_bit_cnt_q;
  assign distr_non_bypass_pop_bit_cnt_d =
      sfifo_distr_pop & sfifo_distr_not_empty & ~es_bypass_mode ?
      distr_non_bypass_pop_bit_cnt_q + DistrFifoWidth :
      distr_non_bypass_pop_bit_cnt_q;

  // Count number of bits pushed into precon FIFO (ObserveFifoWidth wide input, PreCondWidth wide
  // output).
  logic [63:0] precon_push_bit_cnt_d, precon_push_bit_cnt_q;
  assign precon_push_bit_cnt_d = pfifo_precon_push & pfifo_precon_not_full ?
                                 precon_push_bit_cnt_q + ObserveFifoWidth :
                                 precon_push_bit_cnt_q;

  // Assert that as many bits got pushed into the precon FIFO (destination) as got popped from the
  // distr FIFO when bypass mode was disabled (source).
  `ASSERT_AT_RESET_AND_FINAL(DistrFifoPushedIntoPreconFifo_A,
                             precon_push_bit_cnt_q == distr_non_bypass_pop_bit_cnt_q)

  // Track when boot and startup checks are completing.
  logic boot_startup_checks_completing;
  assign boot_startup_checks_completing =
      (u_entropy_src_main_sm.state_q == entropy_src_main_sm_pkg::StartupPass1 &
       u_entropy_src_main_sm.ht_done_pulse_i &
       ~u_entropy_src_main_sm.ht_fail_pulse_i);

  // Track state of boot and startup checks.
  typedef enum logic [1:0] {
    BscStIncomplete,  // checks incomplete
    BscStPassed,      // checks passed
    BscStPushed       // entropy from passed checks pushed
  } bsc_state_e;
  bsc_state_e bsc_state_d, bsc_state_q;
  always_comb begin
    bsc_state_d = bsc_state_q;
    unique case (bsc_state_q)
      BscStIncomplete: begin
        if (boot_startup_checks_completing) begin
          // Checks have just completed.
          bsc_state_d = BscStPassed;
        end
      end
      BscStPassed: begin
        if (main_stage_push) begin
          // Entropy from passed checks is being pushed.
          bsc_state_d = BscStPushed;
        end
      end
      BscStPushed: begin
        // Boot and startup checks remained passed and their entropy pushed until Entropy Source
        // gets disabled again (which is handled below).
        bsc_state_d = bsc_state_q;
      end
      default: bsc_state_d = BscStIncomplete;
    endcase
    // If not enabled, always clear to incomplete.
    if (!mubi4_test_true_strict(mubi_es_enable)) begin
      bsc_state_d = BscStIncomplete;
    end
  end

  // Count number of bits pushed into precon FIFO (ObserveFifoWidth wide input, PreCondWidth wide
  // output) after boot and startup checks.
  logic [63:0] precon_post_startup_push_bit_cnt_d, precon_post_startup_push_bit_cnt_q;
  assign precon_post_startup_push_bit_cnt_d =
      pfifo_precon_push & pfifo_precon_not_full & (bsc_state_q != BscStIncomplete) ?
      precon_post_startup_push_bit_cnt_q + ObserveFifoWidth :
      precon_post_startup_push_bit_cnt_q;

  // Track when esfinal FIFO gets pushed while bypass mode is disabled.
  logic esfinal_non_bypass_push;
  assign esfinal_non_bypass_push = sfifo_esfinal_push & sfifo_esfinal_not_full & ~es_bypass_mode;

  // Count number of bits pushed into esfinal FIFO (SeedLen bits per push) while bypass mode was
  // disabled.
  logic [63:0] esfinal_non_bypass_push_cnt_d, esfinal_non_bypass_push_cnt_q;
  assign esfinal_non_bypass_push_cnt_d = esfinal_non_bypass_push ?
                                         esfinal_non_bypass_push_cnt_q + SeedLen :
                                         esfinal_non_bypass_push_cnt_q;

  // Count number of bits pushed into esfinal FIFO (SeedLen bits per push) after startup checks have
  // passed and while bypass mode was disabled.
  logic [63:0] esfinal_post_startup_push_bit_cnt_d, esfinal_post_startup_push_bit_cnt_q;
  assign esfinal_post_startup_push_bit_cnt_d =
      esfinal_non_bypass_push & (bsc_state_q != BscStIncomplete) ?
      esfinal_post_startup_push_bit_cnt_q + SeedLen :
      esfinal_post_startup_push_bit_cnt_q;

  // Assert that all bits pushed into the esfinal FIFO came from or after passed startup checks.
  `ASSERT_AT_RESET_AND_FINAL(EsfinalFifoPushed_A,
                             esfinal_non_bypass_push_cnt_q == esfinal_post_startup_push_bit_cnt_q)

  // Track result of health tests after boot and startup tests.
  typedef enum logic [1:0] {
    HtStNoResult, // no health test result is currently available
    HtStPassed,   // last health test has passed and entropy has not propagated from conditioner yet
    HtStFailed    // last health test has failed
  } ht_state_e;
  ht_state_e ht_state_d, ht_state_q;
  always_comb begin
    ht_state_d = ht_state_q;
    if (bsc_state_q == BscStPushed) begin
      if (ht_state_q inside {HtStNoResult, HtStFailed}) begin
        if (health_test_done_pulse) begin
          if (!any_fail_pulse && !alert_threshold_fail) begin
            ht_state_d = HtStPassed;
          end else begin
            ht_state_d = HtStFailed;
          end
        end
      end else if (ht_state_q == HtStPassed) begin
        if (main_stage_push_raw) begin
          ht_state_d = HtStNoResult;
        end
      end else begin
        ht_state_d = HtStNoResult;
      end
      if (ht_state_q == HtStFailed) begin
        `ASSERT_I(NoPushAfterFailedHealthTest_A, rst_ni !== 1'b1 || !main_stage_push_raw)
      end
    end
    // If not enabled, always clear to no result.
    if (!mubi4_test_true_strict(mubi_es_enable)) begin
      ht_state_d = HtStNoResult;
    end
  end

  // Track when entropy is expected to get dropped instead of pushed into the esfinal FIFO. This is
  // the case whenever the esfinal FIFO is full. When routing to SW and the SW read finished at the
  // same time, the entropy isn't dropped.
  logic esfinal_exp_drop;
  assign esfinal_exp_drop = sfifo_esfinal_full & (es_route_to_sw ? ~swread_done : 1'b1);

  // Count number of bits that are expected to have gotten pushed into precon FIFO and into esfinal
  // FIFO after boot and startup checks and while bypass mode was disabled.
  logic [63:0] precon_post_startup_exp_push_bit_cnt_d, precon_post_startup_exp_push_bit_cnt_q;
  logic [63:0] esfinal_post_startup_exp_push_bit_cnt_d, esfinal_post_startup_exp_push_bit_cnt_q;
  always_comb begin
    esfinal_post_startup_exp_push_bit_cnt_d = esfinal_post_startup_exp_push_bit_cnt_q;
    precon_post_startup_exp_push_bit_cnt_d = precon_post_startup_exp_push_bit_cnt_q;
    if (bsc_state_q == BscStPassed && bsc_state_d == BscStPushed) begin
      // On the completion of boot and startup checks, SeedLen bits are expected to be pushed into
      // the esfinal FIFO.
      esfinal_post_startup_exp_push_bit_cnt_d += SeedLen;
    end
    if (bsc_state_q != BscStIncomplete && health_test_done_pulse) begin
      // Once boot and startup checks have completed, (4 * health_test_window) bits are expected to
      // have gotten pushed into the precon FIFO.
      precon_post_startup_exp_push_bit_cnt_d += 4 * health_test_window;
    end
    if (ht_state_q == HtStPassed && main_stage_push_raw && !esfinal_exp_drop) begin
      // If none of the health tests failed and the alert threshold has not been exceeded, SeedLen
      // bits are expected to be pushed into the esfinal FIFO -- unless we expect them to get
      // dropped (see above).
      esfinal_post_startup_exp_push_bit_cnt_d += SeedLen;
    end
    // When Entropy Source gets disabled after boot and startup checks have been completed, add the
    // number of bits that have been pushed into precon FIFO since the last conditioner output to
    // the expected number of bits.
    if ((bsc_state_q != BscStIncomplete) && (bsc_state_d == BscStIncomplete)) begin
      logic [63:0] diff_;
      diff_ = precon_post_startup_push_bit_cnt_q - precon_post_startup_exp_push_bit_cnt_q;
      // Assert that the difference is not negative.
      `ASSERT_I(PreconPostStartupDiffNonNegative_A,
                rst_ni !== 1'b1 || (precon_post_startup_push_bit_cnt_q >=
                                    precon_post_startup_exp_push_bit_cnt_q))
      // Assert that the difference is smaller than the number of bits that would have sufficed to
      // get pushed into the conditioner.
      `ASSERT_I(PreconPostStartupDiffSmall_A, rst_ni !== 1'b1 || diff_ < (4 * health_test_window))
      precon_post_startup_exp_push_bit_cnt_d += diff_;
    end
  end
  // This code assumes that `health_test_window` does not change dynamically; capture that in an
  // assertion ensuring it only changes when entropy_src is not enabled.
  `ASSERT(HealthTestWindowStableWhenEnabled_A,
          mubi4_test_true_strict(mubi_es_enable) |-> $stable(health_test_window))

  // Assert that all bits pushed into the esfinal FIFO after startup checks were expected.
  `ASSERT_AT_RESET_AND_FINAL(EsfinalFifoPushedPostStartup_A,
                             esfinal_post_startup_push_bit_cnt_q ==
                             esfinal_post_startup_exp_push_bit_cnt_q)

  // Assert that the expected number of bits pushed into the precon FIFO based on the number of
  // outputs of the conditioner matches the actual number of bits pushed into the precon FIFO after
  // startup checks.  Add a margin (allowed more) as the simulation may end when bits in the precon
  // FIFO have not resulted in conditioner output and Entropy Source has not been disabled.
  logic [63:0] ppspb_allowed_more;
  assign ppspb_allowed_more = bsc_state_q != BscStIncomplete ? 4 * health_test_window : '0;
  `ASSERT_AT_RESET_AND_FINAL(PreconFifoPushedPostStartup_A,
                             `WITHIN_MARGIN(precon_post_startup_push_bit_cnt_q,     // actual
                                            precon_post_startup_exp_push_bit_cnt_q, // expected
                                            0,                                      // allowed less
                                            ppspb_allowed_more))                    // allowed more

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      esbit_push_bit_cnt_q                <= '0;
      esfinal_non_bypass_push_cnt_q       <= '0;
      esfinal_post_startup_push_bit_cnt_q <= '0;
      esrng_push_bit_cnt_q                <= '0;
      postht_from_esbit_push_bit_cnt_q    <= '0;
      postht_from_esrng_push_bit_cnt_q    <= '0;
      postht_non_bypass_pop_bit_cnt_q     <= '0;
      postht_push_bit_cnt_q               <= '0;
      distr_non_bypass_pop_bit_cnt_q      <= '0;
      distr_non_bypass_push_bit_cnt_q     <= '0;
      precon_post_startup_push_bit_cnt_q  <= '0;
      precon_push_bit_cnt_q               <= '0;
      rng_valid_bit_cnt_q                 <= '0;
    end else if (mubi4_test_true_strict(mubi_es_enable) & !fw_ov_mode_entropy_insert) begin
      // All these counters get updated if and only if entropy_src is enabled and the firmware
      // override entropy insertion mode is disabled.  Otherwise, there are no guarantees on how
      // much entropy from the noise source gets dropped due to backpressure.
      esbit_push_bit_cnt_q                <= esbit_push_bit_cnt_d;
      esfinal_non_bypass_push_cnt_q       <= esfinal_non_bypass_push_cnt_d;
      esfinal_post_startup_push_bit_cnt_q <= esfinal_post_startup_push_bit_cnt_d;
      esrng_push_bit_cnt_q                <= esrng_push_bit_cnt_d;
      postht_from_esbit_push_bit_cnt_q    <= postht_from_esbit_push_bit_cnt_d;
      postht_from_esrng_push_bit_cnt_q    <= postht_from_esrng_push_bit_cnt_d;
      postht_non_bypass_pop_bit_cnt_q     <= postht_non_bypass_pop_bit_cnt_d;
      postht_push_bit_cnt_q               <= postht_push_bit_cnt_d;
      distr_non_bypass_pop_bit_cnt_q      <= distr_non_bypass_pop_bit_cnt_d;
      distr_non_bypass_push_bit_cnt_q     <= distr_non_bypass_push_bit_cnt_d;
      precon_post_startup_push_bit_cnt_q  <= precon_post_startup_push_bit_cnt_d;
      precon_push_bit_cnt_q               <= precon_push_bit_cnt_d;
      rng_valid_bit_cnt_q                 <= rng_valid_bit_cnt_d;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      bsc_state_q                             <= BscStIncomplete;
      disable_cnt_q                           <= '0;
      es_delayed_enable_q                     <= '0;
      esfinal_post_startup_exp_push_bit_cnt_q <= '0;
      ht_state_q                              <= HtStNoResult;
      precon_post_startup_exp_push_bit_cnt_q  <= '0;
    end else begin
      bsc_state_q                             <= bsc_state_d;
      disable_cnt_q                           <= disable_cnt_d;
      es_delayed_enable_q                     <= es_delayed_enable_d;
      esfinal_post_startup_exp_push_bit_cnt_q <= esfinal_post_startup_exp_push_bit_cnt_d;
      ht_state_q                              <= ht_state_d;
      precon_post_startup_exp_push_bit_cnt_q  <= precon_post_startup_exp_push_bit_cnt_d;
    end
  end

  // When triggering the conditioner, the precon FIFO must be empty. The postht and distr FIFOs
  // must have been empty in the cycle before. Otherwise, some entropy bits tested as part of the
  // current window won't make into the corresponding seed.
  //
  // In Firmware Override: Extract & Insert mode, we don't care as firmware is responsible for
  // filling the precon FIFO and for triggering the conditioner:
  // - If the conditioner is triggered without the precon FIFO being empty, a recoverable alert is
  //   signaled.
  // - The fill levels of the postht and distr FIFOs are irrelevant for the conditioner in this
  //   mode.
  `ASSERT(FifosEmptyWhenShaProcess_A,
      !fw_ov_mode_entropy_insert && $rose(sha3_process) |->
      $past(!pfifo_postht_not_empty) && $past(!sfifo_distr_not_empty) && !pfifo_precon_not_empty)
`endif

endmodule
