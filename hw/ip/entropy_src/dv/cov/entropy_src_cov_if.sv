// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for entropy_src.
interface entropy_src_cov_if
  import entropy_src_pkg::*;
  import prim_mubi_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,
  mubi8_t     otp_en_entropy_src_fw_read_i,
  mubi8_t     otp_en_entropy_src_fw_over_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import entropy_src_reg_pkg::*;
  import entropy_src_env_pkg::*;
  import entropy_src_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;

  // Resolution to use when converting real sigma values to integers for binning
  real sigma_res = 0.5;

  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup err_test_cg with function sample(bit[4:0] bit_num);
    option.name         = "err_test_cg";
    option.per_instance = 1;

     cp_test_bit: coverpoint bit_num {
       bins valid[] = {0, 1, 2, 20, 21, 22, 28, 29, 30};
     }

  endgroup : err_test_cg

  covergroup mubi_err_cg with function sample(invalid_mubi_e which_mubi);
    option.name         = "mubi_err_cg";
    option.per_instance = 1;

    cp_which_mubi: coverpoint which_mubi;

  endgroup : mubi_err_cg

  covergroup sm_err_cg with function sample(bit ack_sm_err, bit main_sm_err);
    option.name         = "sm_err_cg";
    option.per_instance = 1;

    cp_ack_sm: coverpoint ack_sm_err {
      bins ack_sm = {1};
    }

    cp_main_sm: coverpoint main_sm_err {
      bins main_sm = {1};
    }

  endgroup : sm_err_cg

  covergroup fifo_err_cg with function sample(which_fifo_err_e which_fifo_err,
                                              which_fifo_e which_fifo);
    option.name         = "fifo_err_cg";
    option.per_instance = 1;

    cp_which_fifo: coverpoint which_fifo;

    cp_which_err: coverpoint which_fifo_err;

    cr_fifo_err: cross cp_which_fifo, cp_which_err {
      ignore_bins no_write_err = binsof(cp_which_fifo) intersect { sfifo_esfinal, sfifo_esrng } &&
                                 binsof(cp_which_err) intersect { write };
    }

  endgroup : fifo_err_cg

  covergroup cntr_err_cg with function sample(cntr_e which_cntr,
                                              int which_line,
                                              int which_bucket);
    option.name         = "cntr_err_cg";
    option.per_instance = 1;

    // coverpoint for counters with only one instance
    cp_which_cntr: coverpoint which_cntr {
       bins single_cntrs[] = {window_cntr, repcnts_ht_cntr};
    }

    cp_which_repcnt_line: coverpoint which_line iff(which_cntr == repcnt_ht_cntr) {
      bins repcnt_cntrs[] = { [0:3] };
    }

    cp_which_adaptp_line: coverpoint which_line iff(which_cntr == adaptp_ht_cntr) {
      bins adaptp_cntrs[] = { [0:3] };
    }

    cp_which_markov_line: coverpoint which_line iff(which_cntr == markov_ht_cntr) {
      bins markov_cntrs[] = { [0:3] };
    }

    cp_which_bucket: coverpoint which_bucket iff(which_cntr == bucket_ht_cntr) {
      bins bucket_cntrs[] = { [0:15] };
    }

  endgroup : cntr_err_cg

  // Covergroup to confirm that the entropy_data CSR interface works
  // for all configurations
  covergroup seed_output_csr_cg with function sample(mubi4_t   fips_enable,
                                                     mubi4_t   fips_flag,
                                                     mubi4_t   rng_fips,
                                                     mubi4_t   threshold_scope,
                                                     mubi4_t   rng_bit_enable,
                                                     bit [1:0] rng_bit_sel,
                                                     mubi4_t   es_route,
                                                     mubi4_t   es_type,
                                                     mubi4_t   entropy_data_reg_enable,
                                                     bit [7:0] otp_en_es_fw_read,
                                                     mubi4_t   fw_ov_mode,
                                                     bit [7:0] otp_en_es_fw_over,
                                                     mubi4_t   entropy_insert,
                                                     bit       full_seed);

    option.name         = "seed_output_csr_cg";
    option.per_instance = 1;

    // For the purposes of this CG, ignore coverage of invalid MuBi values
    cp_fips_enable: coverpoint fips_enable iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_fips_flag: coverpoint fips_flag iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_fips: coverpoint rng_fips iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_threshold_scope: coverpoint threshold_scope iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit: coverpoint {rng_bit_enable == MuBi4True, rng_bit_sel} iff(full_seed) {
      bins        enabled[] = { [3'b100 : 3'b111] };
      bins        disabled =  { [3'b000 : 3'b011] };
    }

    // Signal an error if data is observed when es_route is false.
    // Sample this even if we don't have a full seed, to detect partial seed
    // leakage.
    cp_es_route: coverpoint es_route {
      bins         mubi_true  = { MuBi4True };
      illegal_bins mubi_false = { MuBi4False };
    }

    cp_es_type: coverpoint es_type iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Signal an error if data is observed when entropy_data_reg_enable is false
    // Sample this even if we don't have a full seed, to detect partial seed
    // leakage.
    cp_entropy_data_reg_enable: coverpoint entropy_data_reg_enable {
      bins         mubi_true  = { MuBi4True };
      illegal_bins mubi_false = { MuBi4False };
    }

    // Signal an error if data is observed when otp_en_es_fw_read is not true.
    // Sample this even if we don't have a full seed, to detect partial seed
    // leakage.
    cp_otp_en_es_fw_read: coverpoint otp_en_es_fw_read {
      bins         mubi_true  = { MuBi8True };
      illegal_bins mubi_false = { MuBi8False };
      illegal_bins mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    // Sample the FW_OV parameters, just to be sure that they
    // don't interfere with the entropy_data interface.
    cp_fw_ov_mode: coverpoint fw_ov_mode {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Sample the otp_en_entropy_src_fw_over_i input, just to be sure that it
    // does not interfere with the entropy_data interface.
    cp_otp_en_es_fw_over: coverpoint otp_en_es_fw_over {
      bins         mubi_true  = { MuBi8True };
      bins         mubi_false = { MuBi8False };
      bins         mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    cp_entropy_insert: coverpoint entropy_insert {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Cross coverage points

    // Large cross covering entropy data interface over all valid configurations
    cr_config: cross cp_fips_enable, cp_fips_flag, cp_rng_fips, cp_threshold_scope, cp_rng_bit,
                     cp_es_type {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }

    // Finer crosses
    cr_fips_scope: cross cp_fips_enable, cp_threshold_scope;
    cr_fips_bit: cross cp_fips_enable, cp_rng_bit;
    cr_fips_type: cross cp_fips_enable, cp_es_type;
    cr_fips_scope_bit: cross cp_fips_enable, cp_threshold_scope, cp_rng_bit {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }
    cr_fips_scope_type: cross cp_fips_enable, cp_threshold_scope, cp_es_type;
    cr_fips_bit_type: cross cp_fips_enable, cp_rng_bit, cp_es_type;
    cr_scope_bit_type: cross cp_threshold_scope, cp_rng_bit, cp_es_type {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }

    // Entropy data interface functions despite any changes to the fw_ov settings
    cr_fw_ov: cross cp_fw_ov_mode, cp_entropy_insert;

  endgroup : seed_output_csr_cg

  // Covergroup to confirm that the CSRNG HW interface works
  // for all configurations
  covergroup csrng_hw_cg with function sample(bit [3:0] fips_enable,
                                              bit [3:0] fips_flag,
                                              bit [3:0] rng_fips,
                                              bit [3:0] threshold_scope,
                                              bit [3:0] rng_bit_enable,
                                              bit [1:0] rng_bit_sel,
                                              bit [3:0] es_route,
                                              bit [3:0] es_type,
                                              bit [3:0] entropy_data_reg_enable,
                                              bit [7:0] otp_en_es_fw_read,
                                              bit [3:0] fw_ov_mode,
                                              bit [7:0] otp_en_es_fw_over,
                                              bit [3:0] entropy_insert);

    option.name         = "csrng_hw_cg";
    option.per_instance = 1;

    // For the purposes of this CG, ignore coverage of invalid MuBi values
    cp_fips_enable: coverpoint fips_enable {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_fips_flag: coverpoint fips_flag {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_fips: coverpoint rng_fips {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_threshold_scope: coverpoint threshold_scope {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_enable: coverpoint rng_bit_enable{
      bins        enabled  = { MuBi4True };
      bins        disabled = { MuBi4False };
    }

    cp_rng_bit: coverpoint {rng_bit_enable == MuBi4True, rng_bit_sel} {
      bins        enabled[] = { [3'b100 : 3'b111] };
      bins        disabled =  { [3'b000 : 3'b011] };
    }

    // Signal an error if data is observed when es_route is true.
    cp_es_route: coverpoint es_route {
      illegal_bins mubi_true  = { MuBi4True };
      bins         mubi_false = { MuBi4False };
    }

    // This should have no effect on the CSRNG HW IF
    // but we should cover it anyway.
    cp_es_type: coverpoint es_type {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // This should have no effect on the CSRNG HW IF
    // but we should cover it anyway.
    cp_entropy_data_reg_enable: coverpoint entropy_data_reg_enable {
      bins         mubi_true  = { MuBi4True };
      bins         mubi_false = { MuBi4False };
    }

    // This should have no effect on the CSRNG HW IF
    // but we should cover it anyway.
    cp_otp_en_es_fw_read: coverpoint otp_en_es_fw_read {
      bins         mubi_true  = { MuBi8True };
      bins         mubi_false = { MuBi8False };
      bins         mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    // Sample the FW_OV parameters, just to be sure that they
    // don't interfere with the entropy_data interface.
    cp_fw_ov_mode: coverpoint fw_ov_mode {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Sample the otp_en_entropy_src_fw_over_i input, just to be sure that it
    // does not interfere with the entropy_data interface.
    cp_otp_en_es_fw_over: coverpoint otp_en_es_fw_over {
      bins         mubi_true  = { MuBi8True };
      bins         mubi_false = { MuBi8False };
      bins         mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    cp_entropy_insert: coverpoint entropy_insert {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Cross coverage points

    // CSRNG HW interface is tested with all valid configurations
    cr_config: cross cp_fips_enable, cp_threshold_scope, cp_rng_bit_enable,
                     cp_es_type, cp_entropy_data_reg_enable, cp_otp_en_es_fw_read,
                     cp_otp_en_es_fw_over
    {
      // Ignore the invalid mubi values.
      ignore_bins otp_en_es_fw_read_inval =
          ! binsof(cp_otp_en_es_fw_read) intersect {MuBi8True, MuBi8False};
      ignore_bins otp_en_es_fw_over_inval =
          ! binsof(cp_otp_en_es_fw_over) intersect {MuBi8True, MuBi8False};
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit_enable) intersect {MuBi4True};
    }

    // Smaller crosses
    cr_fips_scope_type: cross cp_fips_enable, cp_threshold_scope, cp_es_type;
    cr_fips_scope_data_enable: cross cp_fips_enable, cp_threshold_scope, cp_entropy_data_reg_enable;
    cr_fips_scope_otp: cross cp_fips_enable, cp_threshold_scope, cp_otp_en_es_fw_read,
                             cp_otp_en_es_fw_over;
    cr_fips_scope_fw_ov: cross cp_fips_enable, cp_threshold_scope, cp_fw_ov_mode, cp_entropy_insert;

    cr_fips_bit_type: cross cp_fips_enable, cp_rng_bit, cp_es_type;
    cr_fips_bit_data_enable: cross cp_fips_enable, cp_rng_bit, cp_entropy_data_reg_enable;
    cr_fips_bit_otp: cross cp_fips_enable, cp_rng_bit, cp_otp_en_es_fw_read, cp_otp_en_es_fw_over
    {
      // Ignore the invalid mubi values.
      ignore_bins otp_en_es_fw_read_inval =
          ! binsof(cp_otp_en_es_fw_read) intersect {MuBi8True, MuBi8False};
      ignore_bins otp_en_es_fw_over_inval =
          ! binsof(cp_otp_en_es_fw_over) intersect {MuBi8True, MuBi8False};
    }
    cr_fips_bit_fw_ov: cross cp_fips_enable, cp_rng_bit, cp_fw_ov_mode, cp_entropy_insert;

    cr_scope_bit_type:  cross cp_threshold_scope, cp_rng_bit, cp_es_type {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }
    cr_scope_bit_data_enable:  cross cp_threshold_scope, cp_rng_bit, cp_entropy_data_reg_enable {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }
    cr_scope_bit_otp:  cross cp_threshold_scope, cp_rng_bit, cp_otp_en_es_fw_read,
                             cp_otp_en_es_fw_over {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }
    cr_scope_bit_fw_ov:  cross cp_threshold_scope, cp_rng_bit, cp_fw_ov_mode, cp_entropy_insert {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }

    // CSRNG HW interface functions despite any changes to the fw_ov settings
    cr_fw_ov: cross cp_fw_ov_mode, cp_entropy_insert;

  endgroup : csrng_hw_cg

  // Covergroup to confirm that the Observe FIFO interface works
  // for all configurations
  covergroup observe_fifo_event_cg with function sample(mubi4_t   fips_enable,
                                                        mubi4_t   fips_flag,
                                                        mubi4_t   rng_fips,
                                                        mubi4_t   threshold_scope,
                                                        mubi4_t   rng_bit_enable,
                                                        bit [1:0] rng_bit_sel,
                                                        mubi4_t   es_route,
                                                        mubi4_t   es_type,
                                                        mubi4_t   entropy_data_reg_enable,
                                                        bit [7:0] otp_en_es_fw_read,
                                                        mubi4_t   fw_ov_mode,
                                                        bit [7:0] otp_en_es_fw_over,
                                                        mubi4_t   entropy_insert);

    option.name         = "seed_observe_fifo_event_cg";
    option.per_instance = 1;

    // For the purposes of this CG, ignore coverage of invalid MuBi values

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_fips_enable: coverpoint fips_enable {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
     }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_fips_flag: coverpoint fips_flag {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
     }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_rng_fips: coverpoint rng_fips {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
     }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_threshold_scope: coverpoint threshold_scope {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit: coverpoint {rng_bit_enable == MuBi4True, rng_bit_sel} {
      bins        enabled[] = { [3'b100 : 3'b111] };
      bins        disabled =  { [3'b000 : 3'b011] };
    }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_es_route: coverpoint es_route {
      bins         mubi_true  = { MuBi4True };
      bins         mubi_false = { MuBi4False };
    }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_es_type: coverpoint es_type {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_entropy_data_reg_enable: coverpoint entropy_data_reg_enable {
      bins         mubi_true  = { MuBi4True };
      bins         mubi_false = { MuBi4False };
    }

    // This should have no effect on the Observe FIFO IF
    // but we should cover it anyway.
    cp_otp_en_es_fw_read: coverpoint otp_en_es_fw_read {
      bins         mubi_true  = { MuBi8True };
      bins         mubi_false = { MuBi8False };
      bins         mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    // No data should emerge from the Observe FIFO when disabled
    cp_fw_ov_mode: coverpoint fw_ov_mode {
      bins         mubi_true  = { MuBi4True };
      illegal_bins mubi_false = { MuBi4False };
    }

    // No data should emerge from the Observe FIFO if OTP does not allow it.
    cp_otp_en_es_fw_over: coverpoint otp_en_es_fw_over {
      bins         mubi_true  = { MuBi8True };
      illegal_bins mubi_false = { MuBi8False };
      illegal_bins mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }

    cp_entropy_insert: coverpoint entropy_insert {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Cross coverage points

    // Entropy data interface is tested with all valid configurations
    cr_config: cross cp_fips_enable, cp_threshold_scope, cp_rng_bit, cp_es_route, cp_es_type,
                     cp_entropy_data_reg_enable, cp_otp_en_es_fw_read, cp_otp_en_es_fw_over {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }

    // Smaller cross-points
    cr_rng_insert_fips: cross cp_rng_bit, cp_entropy_insert, cp_fips_enable;
    cr_rng_insert_scope: cross cp_rng_bit, cp_entropy_insert, cp_threshold_scope {
      // The threshold scope needs to be set to false if we are in the single lane mode.
      ignore_bins thresh_scope_true_rng_bit_true =
          binsof(cp_threshold_scope) intersect {MuBi4True} &&
          binsof(cp_rng_bit) intersect { [3'b100 : 3'b111] };
    }
    cr_rng_insert_route: cross cp_rng_bit, cp_entropy_insert, cp_es_route;
    cr_rng_insert_type: cross cp_rng_bit, cp_entropy_insert, cp_es_type;
    cr_rng_insert_reg_en: cross cp_rng_bit, cp_entropy_insert, cp_entropy_data_reg_enable;
    cr_rng_insert_otp: cross cp_rng_bit, cp_entropy_insert, cp_otp_en_es_fw_read,
                             cp_otp_en_es_fw_over;

  endgroup : observe_fifo_event_cg

  covergroup sw_update_cg with function sample(uvm_reg_addr_t offset,
                                               bit sw_regupd,
                                               bit module_enable);

    option.name         = "sw_update_cg";
    option.per_instance = 1;

    cp_lock_state: coverpoint {sw_regupd, module_enable} {
      bins locked_states[] = {2'b00, 2'b01, 2'b11};
    }

    cp_offset: coverpoint offset {
      bins lockable_offsets[] = {
          entropy_src_reg_pkg::ENTROPY_SRC_CONF_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_ENTROPY_CONTROL_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_HEALTH_TEST_WINDOWS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_REPCNT_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_REPCNTS_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_ADAPTP_HI_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_ADAPTP_LO_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_BUCKET_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_MARKOV_HI_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_MARKOV_LO_THRESHOLDS_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_FW_OV_CONTROL_OFFSET,
          entropy_src_reg_pkg::ENTROPY_SRC_OBSERVE_FIFO_THRESH_OFFSET
      };
    }

    cr_cross: cross cp_lock_state, cp_offset;

  endgroup : sw_update_cg

  covergroup sw_disable_cg with function sample(bit me_regwen,
                                                bit module_enable,
                                                entropy_src_main_sm_pkg::state_e main_sm_state);

    option.name         = "sw_disable_cg";
    option.per_instance = 1;

    // Cross SW attempting to disable entropy_src with the state of its main FSM.
    cr_disable_main_sm_state: cross me_regwen, module_enable, main_sm_state {
      // This cross is about disabling, so ignore enables.
      ignore_bins enable = binsof(module_enable) intersect {1'b1};
      // Ignore writes to module_enable when that register is locked because they won't disable
      // entropy_src.
      ignore_bins locked = binsof(me_regwen) intersect {1'b0};
    }

  endgroup : sw_disable_cg

  covergroup enable_delay_cg with function sample(bit enable_i,
                                                  bit esrng_fifo_not_empty_i,
                                                  bit esbit_fifo_not_empty_i,
                                                  bit postht_fifo_not_empty_i,
                                                  bit distr_fifo_not_empty_i,
                                                  bit cs_aes_halt_req_i,
                                                  bit sha3_block_processed_i,
                                                  bit bypass_mode_i,
                                                  bit enable_o);
    option.name         = "enable_delay_cg";
    option.per_instance = 1;

    cp_enable: coverpoint enable_i {
      bins disabling = {1'b0};
      bins enabling = {1'b1};
    }

    // Cover the decision to immediately forward the enable/disable or to delay it.
    cp_enable_io: coverpoint {enable_i, enable_o} {
      bins disable_immediately = {2'b00};
      bins disable_delayed = {2'b01};
      bins enable_delayed = {2'b10};
      bins enable_immediately = {2'b11};
    }

    cp_esrng_fifo: coverpoint esrng_fifo_not_empty_i {
      bins empty = {1'b0};
      bins not_empty = {1'b1};
    }

    cp_esbit_fifo: coverpoint esbit_fifo_not_empty_i {
      bins empty = {1'b0};
      bins not_empty = {1'b1};
    }

    cp_postht_fifo: coverpoint postht_fifo_not_empty_i {
      bins empty = {1'b0};
      bins not_empty = {1'b1};
    }

    cp_distr_fifo: coverpoint distr_fifo_not_empty_i {
      bins empty = {1'b0};
      bins not_empty = {1'b1};
    }

    cr_enable_i_fifo_state: cross cp_enable,
        cp_esrng_fifo, cp_esbit_fifo, cp_postht_fifo, cp_distr_fifo {
      // When re-enabling, all those FIFOs are empty.
      //
      // This is a property of the current implementation and it may be legal to change the
      // implementation so that this no longer holds.  In the current implementation, however, it is
      // impossible to cover these cases.  These cases are thus put into `illegal_bins`, so that
      // they fail if the implementation changes and the coverage has to be redefined.
      illegal_bins enabling_and_any_fifo_not_empty =
          binsof(cp_enable.enabling) && (binsof(cp_esrng_fifo.not_empty) ||
                                         binsof(cp_esbit_fifo.not_empty) ||
                                         binsof(cp_postht_fifo.not_empty) ||
                                         binsof(cp_distr_fifo.not_empty));
    }

    cp_sha3_state: coverpoint {cs_aes_halt_req_i, sha3_block_processed_i} {
      bins idle = {2'b00};
      bins sha3_block_processed = {2'b01};
      bins aes_halt_req = {2'b10};
      bins aes_halt_req_and_sha3_block_processed = {2'b11};
    }

    cr_enable_i_sha3_state: cross cp_enable, cp_sha3_state {
      // SHA3 Block Processed cannot be true when enabling (and thus currently disabled).
      //
      // This is a property of the current implementation and it may be legal to change the
      // implementation so that this no longer holds.  In the current implementation, however, it is
      // impossible to cover these cases.  These cases are thus put into `illegal_bins`, so that
      // they fail if the implementation changes and the coverage has to be redefined.
      illegal_bins enabling_and_sha3_block_processed =
          binsof(cp_enable.enabling) && binsof(cp_sha3_state.sha3_block_processed);
    }

    cr_enable_i_bypass_mode: cross cp_enable, bypass_mode_i;

  endgroup : enable_delay_cg

  // "Shallow" covergroup to validate that the windowed health checks are passing and failing for
  // all possible window sizes
  covergroup win_ht_cg with function sample(health_test_e test_type,
                                            which_ht_e hi_lo,
                                            int window_size,
                                            bit fail);

    option.name         = "win_ht_cg";
    option.per_instance = 1;

    cp_winsize : coverpoint window_size {
      bins common[] = {384, 512, 1024, 2048, 4096};
      bins larger = {8192, 16384, 32768};
    }

    cp_type : coverpoint test_type {
      bins types[] = {adaptp_ht, bucket_ht, markov_ht};
    }

    cp_hi_lo : coverpoint hi_lo;

    cp_fail : coverpoint fail;

    cr_cross : cross cp_winsize, cp_type, cp_hi_lo, cp_fail {
      // bucket_ht does not have a low threshold
      ignore_bins ignore = binsof(cp_type) intersect { bucket_ht } &&
                           binsof(cp_hi_lo) intersect { low_test };
    }

  endgroup : win_ht_cg

  // Most of the arguments to this CG correspond directly to DUT configuration parameters with two
  // exceptions:
  // test_type: Can be repcnt_ht, or repcnts_ht
  // "Score": This is an abstraction of the number of repeated bits that allows us to
  //          compare coverage of the REPCNTS & REPCNT health tests with the same CG.
  //          REPCNTS test values are scaled up by a factor of RNG_BUS_WIDTH to
  //          allow for meaningful comparison in the same set of bins.
  //
  //          Since each _symbol_ repetition is about as coincidentally likely as
  //          RNG_BUS_WIDTH individual line repetitions, the range thresholds for the
  //          symbols the _symbol_ test are lower by the same fraction.  This means
  //          that counting pass/fail-cross-count events is hard to compare between
  //          the two tests unless the repcnts test scores is scaled to use the same
  //          buckets. The scaling is applied in the cg_cont_ht_sample wrapper function
  //          below.
  covergroup cont_ht_cg with function sample(health_test_e test_type,
                                             bit fips_mode,
                                             bit rng_bit_enable,
                                             bit [1:0]  rng_bit_sel,
                                             bit [15:0] score,
                                             bit fail);
    option.name         = "cont_ht_cg";
    option.per_instance = 1;

    cp_type : coverpoint test_type {
      bins types[] = {repcnt_ht, repcnts_ht};
    }

    // Check to see that the thresholds for both boot mode and
    // continuous mode have been tested.
    cp_fips_mode : coverpoint fips_mode;

    cp_fail : coverpoint fail;

    cp_rng_bit: coverpoint {rng_bit_enable, rng_bit_sel} {
      bins        enabled[] = { [3'b100 : 3'b111] };
      bins        disabled =  { [3'b000 : 3'b011] };
    }

    // Don't test threshold, test what HT scores have been observed
    // which is mo
      // re slightly interesting than which thresholds have
    // been applied, as it indicates what range of input RNG values
    // have been seen.
    //
    // The NIST guidelines recommend thresholds that are not so loose
    // that they give false positives less often than once every 2^(40)
    // bits, though they do permit false positive rates in the range of 2^(-20) - 2^(-40)
    // are acceptable.
    //
    // For ideal RNG inputs and this range corrensponds to events in the
    // "medhigh" bin below for the single-line repcnt test, or the "low"
    // bin for the repcnts (4-bit symbol) test.
    //
    cp_score : coverpoint score {
       bins very_low = { [ 1 : 5 ] };
       bins low      = { [ 6 : 10 ] };
       bins medlow   = { [ 11 : 20 ] };
       bins medhigh  = { [ 21 : 40 ] };
       bins high     = { [ 41 : 16'hffff ] };
    }

    // Two way crosses
    cr_type_mode : cross cp_type, cp_fips_mode;

    cr_type_fail : cross cp_type, cp_fail;

    cr_type_rngsel : cross cp_type, cp_rng_bit;

    cr_type_score : cross cp_type, cp_score;

    cr_mode_fail : cross cp_fips_mode, cp_fail;

    cr_mode_rngsel : cross cp_fips_mode, cp_rng_bit;

    cr_mode_score : cross cp_fips_mode, cp_score;

    cr_fail_rngsel : cross cp_fail, cp_rng_bit;

    cr_fail_score : cross cp_fail, cp_score;

    cr_rngsel_score : cross cp_rng_bit, cp_score;

    // Three way crosses
    cr_type_mode_fail : cross cp_type, cp_fips_mode, cp_fail;

    cr_type_mode_rngsel : cross cp_type, cp_fips_mode, cp_rng_bit;

    cr_type_mode_score : cross cp_type, cp_fips_mode, cp_score;

    cr_type_fail_rngsel : cross cp_type, cp_fail, cp_rng_bit;

    cr_type_fail_score : cross cp_type, cp_fail, cp_score;

    cr_type_rngsel_score : cross cp_type, cp_rng_bit, cp_score;

    cr_mode_fail_rngsel : cross cp_fips_mode, cp_fail, cp_rng_bit;

    cr_mode_fail_score : cross cp_fips_mode, cp_fail, cp_score;

    cr_mode_rngsel_score : cross cp_fips_mode, cp_rng_bit, cp_score;

    cr_fail_rngsel_score : cross cp_fail, cp_rng_bit, cp_score;

    // All bin cross
    cr_all : cross cp_type, cp_fips_mode, cp_fail, cp_rng_bit, cp_score;

  endgroup : cont_ht_cg

  // "Deep" covergroup definition to confirm that the threshold performance has been
  // properly tested for a practical range of thresholds for all windowed tests.
  //
  // Covering a range of thesholds for the windowed tests is challenging as the
  // results of the test values are generally expected to be centered around the average
  // value.  Many threshold values will require directed tests to obtain a pass or fail value,
  // if they are even testable at all.
  //
  // Rather than trying to cover all possible threshold ranges with directed tests
  // we focus on a well defined set of bins corresponding to threshold aggressiveness.
  //
  // The most aggressive threshold bin (0-2 sigma) would be most likely to have frequent false
  // positives (at least once every 20 window samples) and HT alerts even when dealing with
  // an ideal stream of RNG inputs.
  //
  // The least aggressive threshold bin (> 6 sigma) more accurately corresponds to the functional
  // mode of operation, with a low rate of false postives, which will require some directed
  // tests to trigger a HT failure.
  //
  // The definition of these practical ranges depends on the size of the windows
  // and the threshold mode (i.e. are statistics accumulated over all RNG lines, or are the
  // thresholds applied on a per-line basis?).  Furthermore, this relationship between the
  // window size and the threshold bins (2-sigma, 4-sigma, 6-sigma, 12-sigma) is non-trivial.
  // That said this covergroup is parameterized in terms of the window size and mode,
  // so unique threshold bins can be constructed for the desired window size.
  // Several instances are then created for a targetted handful of window sizes.
  //

  function automatic unsigned sigma_to_int(real sigma);
    return unsigned'($rtoi($floor(sigma/sigma_res)));
  endfunction

  covergroup win_ht_deep_threshold_cg()
      with function sample(health_test_e test_type,
                           which_ht_e hi_lo,
                           int window_size,
                           bit by_line,
                           real sigma,
                           bit fail);

    option.name         = "win_ht_deep_threshold_cg";
    option.per_instance = 1;

    cp_type : coverpoint test_type {
      bins types[] = {adaptp_ht, bucket_ht, markov_ht};
    }

    // Sharp focus on most important window sizes
    // for this covergroup
    cp_winsize : coverpoint window_size {
      bins sizes[] = {384, 1024, 2048};
    }

    cp_by_line : coverpoint by_line;

    cp_hi_lo : coverpoint hi_lo;

    cp_fail : coverpoint fail;

    cp_threshold : coverpoint sigma_to_int(sigma) {
      // Very frequent false positive rates 1 in 6 for single-sided test
      // (good for testing frequent alert scenarios)
      bins extremely_tight = { [0 : sigma_to_int(1.0) - 1]};
      // False positive rate > 2.5% (for testing frequent single failures)
      bins very_tight      = { [sigma_to_int(1.0) : sigma_to_int(2.0) - 1] };
      // False positive rate > 3ppm (almost covers up to SP 800-90B's minimum suggested 1 in 2^20)
      bins tight           = { [sigma_to_int(2.0) : sigma_to_int(4.5) - 1] };
      // False positive rate > 1.25 in 1e12 (covers to most of SP 800-90B range down to 1 in 2^40)
      bins typical         = { [sigma_to_int(4.5) : sigma_to_int(7.0) - 1] };
      // All other possible sigma values
      bins loose           = { [sigma_to_int(7.0) : 32'hffff_ffff] };
    }

    cr_cross : cross cp_winsize, cp_by_line, cp_type, cp_hi_lo, cp_fail, cp_threshold {
      // bucket_ht does not have a low threshold
      ignore_bins ignore_a = binsof(cp_type) intersect { bucket_ht } &&
                             binsof(cp_hi_lo) intersect { low_test };
      // by_line mode does not apply to bucket_ht
      ignore_bins ignore_b = binsof(cp_type) intersect { bucket_ht } &&
                             binsof(cp_by_line) intersect { 1 };
    }

  endgroup : win_ht_deep_threshold_cg

  covergroup alert_cnt_cg with function sample(bit [15:0] threshold, bit has_fired);

    option.name         = "alert_cnt_cg";
    option.per_instance = 1;

    cp_threshold : coverpoint threshold {
      bins one     = {1};
      bins two     = {2};
      bins high    = { [3:6] };
      bins higher  = { [7:10] };
      bins highest = { [11:16'hffff] };
    }

    // We sample this coverpoint both when the setting is applied at the register
    // and when the alert is detected.
    cp_has_fired : coverpoint has_fired;

    cr_cross : cross cp_threshold, cp_has_fired {
      // For the highest bin (>10) it is unlikely that one would actually use this bin, and it
      // would be particularly time intensive to check that the highest values are reached.  Thus
      // we do not require coverage to check that alerts are observed for this bin.
      ignore_bins ignore_a= binsof(cp_threshold) intersect { 16'hffff } &&
                            binsof(cp_has_fired) intersect { 1 };
    }
  endgroup : alert_cnt_cg

  covergroup observe_fifo_threshold_cg with function sample(int threshold);

    option.name         = "observe_fifo_threshold_cg";
    option.per_instance = 1;

    cp_threshold : coverpoint threshold {
      bins one = {1};
      bins quartiles[4] = { [2:62] };
      bins max = { 63 };
    }

  endgroup : observe_fifo_threshold_cg

  covergroup one_way_ht_threshold_reg_cg with function sample(int offset,
                                                              bit rejected,
                                                              bit is_fips);

    option.name         = "one_way_ht_threshold_cg";
    option.per_instance = 1;

    cp_offset : coverpoint offset {
      bins one_way_regs[] = {
        entropy_src_reg_pkg::ENTROPY_SRC_REPCNT_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_REPCNTS_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_ADAPTP_HI_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_ADAPTP_LO_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_BUCKET_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_MARKOV_HI_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_MARKOV_LO_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_EXTHT_HI_THRESHOLDS_OFFSET,
        entropy_src_reg_pkg::ENTROPY_SRC_EXTHT_LO_THRESHOLDS_OFFSET
      };
    }

    cp_rejected : coverpoint rejected;

    cp_is_fips : coverpoint is_fips;

    cr_cross : cross cp_rejected, cp_offset, cp_is_fips;

  endgroup : one_way_ht_threshold_reg_cg

  covergroup recov_alert_cg with function sample(int alert_bit);
    option.name         = "recov_alert_cg";
    option.per_instance = 1;

    cp_alert_bit : coverpoint alert_bit {
      bins alert_bits[] = {0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
    }
  endgroup : recov_alert_cg


  `DV_FCOV_INSTANTIATE_CG(err_test_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(mubi_err_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(sm_err_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(fifo_err_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(cntr_err_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(seed_output_csr_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_hw_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(observe_fifo_event_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(sw_update_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(sw_disable_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(enable_delay_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(cont_ht_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(win_ht_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(win_ht_deep_threshold_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(alert_cnt_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(observe_fifo_threshold_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(one_way_ht_threshold_reg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(recov_alert_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_err_test_sample(bit [4:0] err_code);
    err_test_cg_inst.sample(err_code);
  endfunction

  function automatic void cg_mubi_err_sample(invalid_mubi_e which_mubi);
    mubi_err_cg_inst.sample(which_mubi);
  endfunction

  function automatic void cg_sm_err_sample(bit ack_sm_err, bit main_sm_err);
    sm_err_cg_inst.sample(ack_sm_err, main_sm_err);
  endfunction

  function automatic void cg_fifo_err_sample(which_fifo_err_e which_fifo_err,
                                             which_fifo_e which_fifo);
    fifo_err_cg_inst.sample(which_fifo_err, which_fifo);
  endfunction

  function automatic void cg_cntr_err_sample(cntr_e which_cntr,
                                             int which_line,
                                             int which_bucket);
    cntr_err_cg_inst.sample(which_cntr, which_line, which_bucket);
  endfunction

  function automatic void cg_seed_output_csr_sample(mubi4_t   fips_enable,
                                                    mubi4_t   fips_flag,
                                                    mubi4_t   rng_fips,
                                                    mubi4_t   threshold_scope,
                                                    mubi4_t   rng_bit_enable,
                                                    bit [1:0] rng_bit_sel,
                                                    mubi4_t   es_route,
                                                    mubi4_t   es_type,
                                                    mubi4_t   entropy_data_reg_enable,
                                                    bit [7:0] otp_en_es_fw_read,
                                                    mubi4_t   fw_ov_mode,
                                                    bit [7:0] otp_en_es_fw_over,
                                                    mubi4_t   entropy_insert,
                                                    bit       full_seed);
    seed_output_csr_cg_inst.sample(fips_enable, fips_flag, rng_fips, threshold_scope,
                                   rng_bit_enable, rng_bit_sel, es_route, es_type,
                                   entropy_data_reg_enable, otp_en_es_fw_read, fw_ov_mode,
                                   otp_en_es_fw_over, entropy_insert, full_seed);
  endfunction

  function automatic void cg_csrng_hw_sample(bit [3:0] fips_enable,
                                             bit [3:0] fips_flag,
                                             bit [3:0] rng_fips,
                                             bit [3:0] threshold_scope,
                                             bit [3:0] rng_bit_enable,
                                             bit [1:0] rng_bit_sel,
                                             bit [3:0] es_route,
                                             bit [3:0] es_type,
                                             bit [3:0] entropy_data_reg_enable,
                                             bit [7:0] otp_en_es_fw_read,
                                             bit [3:0] fw_ov_mode,
                                             bit [7:0] otp_en_es_fw_over,
                                             bit [3:0] entropy_insert);
    csrng_hw_cg_inst.sample(fips_enable, fips_flag, rng_fips, threshold_scope, rng_bit_enable,
                            rng_bit_sel, es_route, es_type, entropy_data_reg_enable,
                            otp_en_es_fw_read, fw_ov_mode, otp_en_es_fw_over, entropy_insert);
  endfunction

  function automatic void cg_observe_fifo_event_sample(mubi4_t   fips_enable,
                                                       mubi4_t   fips_flag,
                                                       mubi4_t   rng_fips,
                                                       mubi4_t   threshold_scope,
                                                       mubi4_t   rng_bit_enable,
                                                       bit [1:0] rng_bit_sel,
                                                       mubi4_t   es_route,
                                                       mubi4_t   es_type,
                                                       mubi4_t   entropy_data_reg_enable,
                                                       bit [7:0] otp_en_es_fw_read,
                                                       mubi4_t   fw_ov_mode,
                                                       bit [7:0] otp_en_es_fw_over,
                                                       mubi4_t   entropy_insert);
    observe_fifo_event_cg_inst.sample(fips_enable, fips_flag, rng_fips, threshold_scope,
                                      rng_bit_enable, rng_bit_sel, es_route, es_type,
                                      entropy_data_reg_enable, otp_en_es_fw_read, fw_ov_mode,
                                      otp_en_es_fw_over, entropy_insert);
  endfunction

  function automatic void cg_sw_update_sample(uvm_pkg::uvm_reg_addr_t offset,
                                              bit sw_regupd,
                                              bit module_enable);
    string msg, fmt;

    sw_update_cg_inst.sample(offset, sw_regupd, module_enable);

  endfunction

  function automatic void cg_sw_disable_sample(bit me_regwen,
                                               bit module_enable,
                                               entropy_src_main_sm_pkg::state_e main_sm_state);
    sw_disable_cg_inst.sample(me_regwen, module_enable, main_sm_state);

  endfunction

  // Please see the note near the definition of cont_ht_cg describing the scoring of the
  // repcnts test, and applying bins for both the repcnt and
  function automatic void cg_cont_ht_sample(health_test_e test_type,
                                            bit fips_mode,
                                            bit rng_bit_enable,
                                            bit [1:0] rng_bit_select,
                                            bit [15:0] raw_score,
                                            bit fail);
    bit [15:0] score;
    bit [31:0] symbol_score;

    symbol_score = (32'(raw_score) * RNG_BUS_WIDTH > 32'hffff) ?
                   32'hffff : 32'(raw_score) * RNG_BUS_WIDTH;
    score = (test_type == repcnts_ht) ? symbol_score[15:0] : raw_score;

    cont_ht_cg_inst.sample(test_type, fips_mode, rng_bit_enable, rng_bit_select, score, fail);

  endfunction

  function automatic void cg_win_ht_sample(health_test_e test_type,
                                           which_ht_e hi_low,
                                           int window_size,
                                           bit fail);
    win_ht_cg_inst.sample(test_type,
                          hi_low,
                          window_size,
                          fail);
  endfunction

  function automatic void cg_win_ht_deep_threshold_sample(health_test_e test_type,
                                                         which_ht_e hi_low,
                                                         int window_size,
                                                         bit by_line,
                                                         real sigma,
                                                         bit fail);
    win_ht_deep_threshold_cg_inst.sample(test_type,
                                         hi_low,
                                         window_size,
                                         by_line,
                                         sigma,
                                         fail);
  endfunction

  function automatic void cg_alert_cnt_sample(int threshold, bit has_fired);
    alert_cnt_cg_inst.sample(threshold, has_fired);
  endfunction

  function automatic void cg_observe_fifo_threshold_sample(int threshold);
    observe_fifo_threshold_cg_inst.sample(threshold);
  endfunction

  function automatic void cg_one_way_ht_threshold_reg_sample(int offset, bit rejected, bit fips);
    one_way_ht_threshold_reg_cg_inst.sample(offset, rejected, fips);
  endfunction

  function automatic void cg_recov_alert_sample(int which_bit);
    recov_alert_cg_inst.sample(which_bit);
  endfunction


  // Sample the csrng_hw_cg whenever data is output on the csrng pins
  logic csrng_if_req, csrng_if_ack;
  mubi4_t fips_enable_csr, threshold_scope_csr, rng_bit_enable_csr, rng_bit_sel_csr, es_route_csr,
          es_type_csr, entropy_data_reg_enable_csr, fw_ov_mode_csr, entropy_insert_csr;
  mubi8_t otp_en_es_fw_read_val;

  assign csrng_if_req = tb.dut.entropy_src_hw_if_i.es_req;
  assign csrng_if_ack = tb.dut.entropy_src_hw_if_o.es_ack;

  logic enable_q, enable_qq;

  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      enable_q  <= 1'b0;
      enable_qq <= 1'b0;
    end else begin
      enable_qq <= enable_q;
      enable_q  <= tb.dut.u_entropy_src_core.u_enable_delay.enable_i;

      if(csrng_if_req && csrng_if_ack) begin
        cg_csrng_hw_sample(tb.dut.reg2hw.conf.fips_enable.q,
                           tb.dut.reg2hw.conf.fips_flag.q,
                           tb.dut.reg2hw.conf.rng_fips.q,
                           tb.dut.reg2hw.conf.threshold_scope.q,
                           tb.dut.reg2hw.conf.rng_bit_enable.q,
                           tb.dut.reg2hw.conf.rng_bit_sel.q,
                           tb.dut.reg2hw.entropy_control.es_route.q,
                           tb.dut.reg2hw.entropy_control.es_type.q,
                           tb.dut.reg2hw.conf.entropy_data_reg_enable.q,
                           otp_en_entropy_src_fw_read_i,
                           tb.dut.reg2hw.fw_ov_control.fw_ov_mode.q,
                           otp_en_entropy_src_fw_over_i,
                           tb.dut.reg2hw.fw_ov_control.fw_ov_entropy_insert.q);
      end

      if (enable_qq != enable_q) begin
        // Only sample this CG when the enable signal changes.
        enable_delay_cg_inst.sample(
            enable_q,
            tb.dut.u_entropy_src_core.u_enable_delay.esrng_fifo_not_empty_i,
            tb.dut.u_entropy_src_core.u_enable_delay.esbit_fifo_not_empty_i,
            tb.dut.u_entropy_src_core.u_enable_delay.postht_fifo_not_empty_i,
            tb.dut.u_entropy_src_core.u_enable_delay.distr_fifo_not_empty_i,
            tb.dut.u_entropy_src_core.u_enable_delay.cs_aes_halt_req_i,
            tb.dut.u_entropy_src_core.u_enable_delay.sha3_block_processed_i,
            tb.dut.u_entropy_src_core.u_enable_delay.bypass_mode_i,
            tb.dut.u_entropy_src_core.u_enable_delay.enable_o);
      end
    end
  end

endinterface : entropy_src_cov_if
