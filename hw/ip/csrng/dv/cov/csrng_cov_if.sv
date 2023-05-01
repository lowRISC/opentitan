// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for csrng.

interface csrng_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import csrng_pkg::*;
  import csrng_agent_pkg::*;
  import csrng_env_pkg::*;
  import prim_mubi_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  logic [1:0] hw0_cmd_depth;
  logic [1:0] hw1_cmd_depth;
  logic [1:0] sw_cmd_depth;

  logic hw0_cmd_rdy, hw0_cmd_vld, hw0_cmd_pop;
  logic hw1_cmd_rdy, hw1_cmd_vld, hw1_cmd_pop;
  logic sw_cmd_rdy, sw_cmd_vld, sw_cmd_pop;

  logic hw0_genbits_rdy, hw0_genbits_vld, hw0_genbits_depth;
  logic hw1_genbits_rdy, hw1_genbits_vld, hw1_genbits_depth;
  logic sw_genbits_rdy, sw_genbits_vld, sw_genbits_depth;

  assign hw0_cmd_depth = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.sfifo_cmd_depth;
  assign hw1_cmd_depth = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.sfifo_cmd_depth;
  assign sw_cmd_depth = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.sfifo_cmd_depth;

  assign hw0_genbits_depth =
    u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.u_prim_fifo_genbits.depth_o;
  assign hw1_genbits_depth =
    u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.u_prim_fifo_genbits.depth_o;
  assign sw_genbits_depth =
    u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.u_prim_fifo_genbits.depth_o;

  assign hw0_cmd_vld = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.cmd_stage_vld_i;
  assign hw0_cmd_rdy = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.cmd_stage_rdy_o;
  assign hw0_cmd_pop = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.cmd_fifo_pop;
  assign hw1_cmd_vld = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.cmd_stage_vld_i;
  assign hw1_cmd_rdy = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.cmd_stage_rdy_o;
  assign hw1_cmd_pop = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.cmd_fifo_pop;
  assign sw_cmd_vld = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.cmd_stage_vld_i;
  assign sw_cmd_rdy = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.cmd_stage_rdy_o;
  assign sw_cmd_pop = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.cmd_fifo_pop;

  assign hw0_genbits_vld = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.genbits_vld_o;
  assign hw0_genbits_rdy = u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage.genbits_rdy_i;
  assign hw1_genbits_vld = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.genbits_vld_o;
  assign hw1_genbits_rdy = u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage.genbits_rdy_i;
  assign sw_genbits_vld = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.genbits_vld_o;
  assign sw_genbits_rdy = u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage.genbits_rdy_i;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup csrng_sfifo_cg @(posedge clk_i);
    option.name         = "csrng_sfifo_cg";
    option.per_instance = 1;

    // HW0 App
    cp_hw0_cmd_depth: coverpoint hw0_cmd_depth{
      illegal_bins more_than_depth = {3};
    }
    cp_hw0_genbits_depth: coverpoint hw0_genbits_depth;
    hw0_cmd_push_cross: cross cp_hw0_cmd_depth, hw0_cmd_vld, hw0_cmd_rdy{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to be not full and not ready / full and ready.
      // We thus use assertions to detect such illegal states that can be disabled if needed.
      ignore_bins not_full_and_not_ready = !binsof(cp_hw0_cmd_depth) intersect {2}
                                           with (!hw0_cmd_rdy);
      ignore_bins full_and_ready = binsof(cp_hw0_cmd_depth) intersect {2} with (hw0_cmd_rdy);
    }
    hw0_cmd_pop_cross: cross cp_hw0_cmd_depth, hw0_cmd_pop{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to get read while being empty. If that happens,
      // a fatal alert must be signaled. However, multiple FIFO error conditions are collected
      // in the same alert, we don't need to test every possible alert condition for every
      // possible FIFO and thus ignore this particular cross point.
      ignore_bins empty_and_pop = binsof(cp_hw0_cmd_depth) intersect {0}
                                  with (hw0_cmd_pop);
    }
    hw0_genbits_pop_cross: cross cp_hw0_genbits_depth, hw0_genbits_vld, hw0_genbits_rdy{
      // Note: cs_enable factors into vld_o. If the module is disabled, vld_o may still be low
      // despite the FIFO being full. This is thus not an illegal bin, the disable/re-enable
      // testing will help us to hit those cross points.
      illegal_bins empty_and_valid =
        binsof(cp_hw0_genbits_depth) intersect {0} with (hw0_genbits_vld);
    }

    // HW1 App
    cp_hw1_cmd_depth: coverpoint hw1_cmd_depth{
      illegal_bins more_than_depth = {3};
    }
    cp_hw1_genbits_depth: coverpoint hw1_genbits_depth;
    hw1_cmd_push_cross: cross cp_hw1_cmd_depth, hw1_cmd_vld, hw1_cmd_rdy{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to be not full and not ready / full and ready.
      // We thus use assertions to detect such illegal states that can be disabled if needed.
      ignore_bins not_full_and_not_ready = !binsof(cp_hw1_cmd_depth) intersect {2}
                                           with (!hw1_cmd_rdy);
      ignore_bins full_and_ready = binsof(cp_hw1_cmd_depth) intersect {2} with (hw1_cmd_rdy);
    }
    hw1_cmd_pop_cross: cross cp_hw1_cmd_depth, hw1_cmd_pop{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to get read while being empty. If that happens,
      // a fatal alert must be signaled. However, multiple FIFO error conditions are collected
      // in the same alert, we don't need to test every possible alert condition for every
      // possible FIFO and thus ignore this particular cross point.
      ignore_bins empty_and_pop = binsof(cp_hw1_cmd_depth) intersect {0}
                                  with (hw1_cmd_pop);
    }
    hw1_genbits_pop_cross: cross cp_hw1_genbits_depth, hw1_genbits_vld, hw1_genbits_rdy{
      // Note: cs_enable factors into vld_o. If the module is disabled, vld_o may still be low
      // despite the FIFO being full. This is thus not an illegal bin, the disable/re-enable
      // testing will help us to hit those cross points.
      illegal_bins empty_and_valid =
        binsof(cp_hw1_genbits_depth) intersect {0} with (hw1_genbits_vld);
    }

    // SW App
    cp_sw_cmd_depth: coverpoint sw_cmd_depth{
      illegal_bins more_than_depth = {3};
    }
    cp_sw_genbits_depth: coverpoint sw_genbits_depth;
    sw_cmd_push_cross: cross cp_sw_cmd_depth, sw_cmd_vld, sw_cmd_rdy{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to be not full and not ready / full and ready.
      // We thus use assertions to detect such illegal states that can be disabled if needed.
      ignore_bins not_full_and_not_ready = !binsof(cp_sw_cmd_depth) intersect {2}
                                           with (!sw_cmd_rdy);
      ignore_bins full_and_ready = binsof(cp_sw_cmd_depth) intersect {2} with (sw_cmd_rdy);
    }
    sw_cmd_pop_cross: cross cp_sw_cmd_depth, sw_cmd_pop{
      // Note: The csrng_err and csrng_intr tests inject different types of errors into various
      // FIFOs which may cause the command FIFOs to get read while being empty. If that happens,
      // a fatal alert must be signaled. However, multiple FIFO error conditions are collected
      // in the same alert, we don't need to test every possible alert condition for every
      // possible FIFO and thus ignore this particular cross point.
      ignore_bins empty_and_pop = binsof(cp_sw_cmd_depth) intersect {0}
                                  with (sw_cmd_pop);
    }
    sw_genbits_pop_cross: cross cp_sw_genbits_depth, sw_genbits_vld, sw_genbits_rdy{
      // Note: cs_enable factors into vld_o. If the module is disabled, vld_o may still be low
      // despite the FIFO being full. This is thus not an illegal bin, the disable/re-enable
      // testing will help us to hit those cross points.
      illegal_bins empty_and_valid =
        binsof(cp_sw_genbits_depth) intersect {0} with (sw_genbits_vld);
    }

    // Crosses between Apps
    cmd_depth_cross: cross cp_hw0_cmd_depth, cp_hw1_cmd_depth, cp_sw_cmd_depth;
    genbits_depth_cross: cross cp_hw0_genbits_depth, cp_hw1_genbits_depth, cp_sw_genbits_depth;
  endgroup : csrng_sfifo_cg


  covergroup csrng_cfg_cg with function sample(bit [7:0] otp_en_cs_sw_app_read,
                                               bit [3:0] lc_hw_debug_en,
                                               mubi4_t   sw_app_enable,
                                               mubi4_t   read_int_state,
                                               bit       regwen,
                                               bit [3:0] enable
                                              );
    option.name         = "csrng_cfg_cg";
    option.per_instance = 1;

    cp_enable: coverpoint enable {
      bins mubi_true  = { MuBi4True };
      bins mubi_false = { MuBi4False };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi4True, MuBi4False }));
    }
    cp_sw_app_read:    coverpoint otp_en_cs_sw_app_read {
      bins mubi_true  = { MuBi8True };
      bins mubi_false = { MuBi8False };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi8True, MuBi8False }));
    }
    cp_lc_hw_debug_en: coverpoint lc_hw_debug_en {
      bins lc_on    = { lc_ctrl_pkg::On };
      bins lc_off   = { lc_ctrl_pkg::Off };
      bins lc_inval = { [0:$] } with (!(item inside { lc_ctrl_pkg::On, lc_ctrl_pkg::Off }));
    }
    cp_sw_app_enable:  coverpoint sw_app_enable;
    cp_read_int_state: coverpoint read_int_state;
    cp_regwen:         coverpoint regwen;

    sw_app_read_sw_app_enable_cross: cross cp_sw_app_read, cp_sw_app_enable;
  endgroup : csrng_cfg_cg

  covergroup csrng_sts_cg with function sample();
    option.name         = "csrng_sts_cg";
    option.per_instance = 1;

    cp_hw_inst_exc: coverpoint u_reg.hw_exc_sts_qs[NUM_HW_APPS-1:0] {
      bins no_exc  = { 0 };
      bins hw0_exc = { 1 };
      bins hw1_exc = { 2 };
      bins sim_exc = { 3 }; // simultaneous exception on both HW app interfaces
    }

    cp_sw_cmd_sts_cmd_rdy: coverpoint u_reg.sw_cmd_sts_cmd_rdy_qs {
      bins not_ready = { 1'b0 };
      bins ready     = { 1'b1 };
    }

    cp_sw_cmd_sts_cmd_sts: coverpoint u_reg.sw_cmd_sts_cmd_sts_qs {
      bins success = { 1'b0 };
      bins error   = { 1'b1 };
    }

  endgroup : csrng_sts_cg

  covergroup csrng_err_code_cg with function sample(err_code_bit_e err_code_bit,
                                                    bit [2:0] fifo_err_type);
    option.name         = "csrng_err_code_cg";
    option.per_instance = 1;

    cp_err_codes: coverpoint err_code_bit{
      // This is covered separately as it's about reporting the type of SFIFO failure
      ignore_bins fifo_type = { FIFO_WRITE_ERR, FIFO_READ_ERR, FIFO_STATE_ERR };
    }

    cp_fifo_err_type: coverpoint fifo_err_type{
      wildcard bins no_err    = { 3'b000 };
      wildcard bins write_err = { 3'b??1 };
      wildcard bins read_err  = { 3'b?1? };
      wildcard bins state_err = { 3'b1?? };
    }

    fifo_err_type_cross: cross cp_err_codes, cp_fifo_err_type{
      // If ERR_CODE register has SFIFO related field set, it also needs to set at least one
      // FIFO_*_ERR field.
      illegal_bins illegal = !binsof(cp_err_codes) intersect { CMD_STAGE_SM_ERR, MAIN_SM_ERR,
                                                               DRBG_GEN_SM_ERR, DRBG_UPDBE_SM_ERR,
                                                               DRBG_UPDOB_SM_ERR, AES_CIPHER_SM_ERR,
                                                               CMD_GEN_CNT_ERR } &&
                             binsof(cp_fifo_err_type) intersect { 0 };

      ignore_bins ignore = binsof(cp_err_codes) intersect { CMD_STAGE_SM_ERR, MAIN_SM_ERR,
                                                            DRBG_GEN_SM_ERR, DRBG_UPDBE_SM_ERR,
                                                            DRBG_UPDOB_SM_ERR, AES_CIPHER_SM_ERR,
                                                            CMD_GEN_CNT_ERR };
    }

    cp_csrng_aes_fsm_err: coverpoint
      u_csrng_core.u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control.mr_alert {
      bins        no_err = { 0 };
      bins        rail_0 = { 1 };
      bins        rail_1 = { 2 };
      bins        rail_2 = { 4 };
      ignore_bins other  = { 3, [5:7]};
    }

  endgroup : csrng_err_code_cg

  covergroup csrng_err_code_test_cg with function sample(err_code_bit_e err_test);
    option.name         = "csrng_err_code_test_cg";
    option.per_instance = 1;

    err_code_test_cp: coverpoint err_test;

  endgroup : csrng_err_code_test_cg

  covergroup csrng_recov_alert_sts_cg with function sample(recov_alert_bit_e recov_alert);
    option.name         = "csrng_recov_alert_sts_cg";
    option.per_instance = 1;

    recov_alert_sts_cp: coverpoint recov_alert;
  endgroup : csrng_recov_alert_sts_cg

  covergroup csrng_cmds_cg with function sample(bit [NUM_HW_APPS-1:0] app,
                                                acmd_e                acmd,
                                                bit [3:0]             clen,
                                                bit [3:0]             flags,
                                                bit [11:0]            glen
                                               );
    option.name         = "csrng_cmds_cg";
    option.per_instance = 1;

    cp_app: coverpoint app {
      bins        hw_app0 = { 0 };
      bins        hw_app1 = { 1 };
      bins        sw_app  = { 2 };
      ignore_bins other   = { 3 };
    }

    cp_acmd: coverpoint acmd {
      bins  Instantiate   = { INS };
      bins  Reseed        = { RES };
      bins  Generate      = { GEN };
      bins  Update        = { UPD };
      bins  Uninstantiate = { UNI };
      bins  Reserved      = { INV, GENB, GENU };
    }

    cp_clen: coverpoint clen {
      bins zero         = { 0 };
      bins one          = { 1 };
      bins two          = { 2 };
      bins three        = { 3 };
      bins four         = { 4 };
      bins five         = { 5 };
      bins six          = { 6 };
      bins seven        = { 7 };
      bins eight        = { 8 };
      bins nine         = { 9 };
      bins ten          = { 10 };
      bins eleven       = { 11 };
      bins twelve       = { 12 };
      ignore_bins other = { [13:15] };
    }

    cp_flags: coverpoint flags {
      bins mubi_false = { MuBi4False };
      bins mubi_true  = { MuBi4True };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi4True, MuBi4False }));
    }

    cp_glen: coverpoint glen {
      bins one         = { 1 };
      bins multiple    = { [2:$] };
      ignore_bins zero = { 0 };
    }

    app_acmd_cross: cross cp_app, cp_acmd {
      ignore_bins invalid = binsof(cp_acmd) intersect { INV, GENB, GENU };
    }

    acmd_clen_cross: cross cp_acmd, cp_clen {
      ignore_bins invalid = binsof(cp_acmd) intersect { UNI, INV, GENB, GENU } &&
                            binsof(cp_clen) intersect { [1:$] };
    }

    acmd_flags_cross: cross cp_acmd, cp_flags {
      ignore_bins invalid = binsof(cp_acmd) intersect { INV, GENB, GENU };
    }

    acmd_glen_cross: cross cp_acmd, cp_glen {
      ignore_bins invalid = binsof(cp_acmd) intersect { INV, GENB, GENU };
    }

    flags_clen_acmd_cross: cross cp_acmd, cp_flags, cp_clen {
      // Use only Entropy Source seed
      bins ins_only_entropy_src_seed = binsof(cp_flags) intersect { MuBi4False } &&
                                       binsof(cp_clen)  intersect { 0 } &&
                                       binsof(cp_acmd)  intersect { INS };
      bins res_only_entropy_src_seed = binsof(cp_flags) intersect { MuBi4False } &&
                                       binsof(cp_clen)  intersect { 0 } &&
                                       binsof(cp_acmd)  intersect { RES };
      // Use Entropy Source Seed ^ Additional Data (clen)
      bins ins_xored_entropy_src_seed = binsof(cp_flags) intersect { MuBi4False } &&
                                        binsof(cp_clen)  intersect { [1:$] } &&
                                        binsof(cp_acmd)  intersect { INS };
      bins res_xored_entropy_src_seed = binsof(cp_flags) intersect { MuBi4False } &&
                                        binsof(cp_clen)  intersect { [1:$] } &&
                                        binsof(cp_acmd)  intersect { RES };
      // Use zero as seed
      bins ins_zero_seed = binsof(cp_flags) intersect { MuBi4True } &&
                           binsof(cp_clen)  intersect { 0 } &&
                           binsof(cp_acmd)  intersect { INS };
      bins res_zero_seed = binsof(cp_flags) intersect { MuBi4True } &&
                           binsof(cp_clen)  intersect { 0 } &&
                           binsof(cp_acmd)  intersect { RES };
      // Use Additional Data (clen) as seed
      bins ins_add_data_seed = binsof(cp_flags) intersect { MuBi4True } &&
                               binsof(cp_clen)  intersect { [1:$] } &&
                               binsof(cp_acmd)  intersect { INS };
      bins res_add_data_seed = binsof(cp_flags) intersect { MuBi4True } &&
                               binsof(cp_clen)  intersect { [1:$] } &&
                               binsof(cp_acmd)  intersect { RES };
      // Since other modes are not related with flag0, ignore them in this cross.
      ignore_bins ignore_other_cmds = binsof(cp_acmd) intersect { UPD, UNI, GEN, INV, GENB, GENU };
      // Ignore invalid MuBi values for flags.
      ignore_bins ignore_invalid_mubi = !binsof(cp_flags) intersect { MuBi4True, MuBi4False };
    }
  endgroup : csrng_cmds_cg

  // Covergroup to sample otp_en_cs_sw_app_read feature
  covergroup csrng_otp_en_sw_app_read_cg with function sample(
    bit read_int_state_val_reg,
    bit read_genbits_reg,
    bit [7:0] otp_en_cs_sw_app_read,
    bit [3:0] read_int_state,
    bit [3:0] sw_app_enable
  );
    option.per_instance  = 1;
    option.name          = "csrng_otp_en_sw_app_read_cg";
    // Coverpoint for register read to INT_STATE_VAL
    cp_read_int_state_val: coverpoint read_int_state_val_reg {
      bins read = { 1'b1 };
    }
    // Coverpoint for register read to GENBITS
    cp_read_genbits_reg: coverpoint read_genbits_reg {
      bins read = { 1'b1 };
    }
    // Cover values of OTP_EN_CSRNG_SW_APP_READ signal
    cp_otp_en_cs_sw_app_read: coverpoint otp_en_cs_sw_app_read {
      bins mubi_true  = { MuBi8True };
      bins mubi_false = { MuBi8False };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi8True, MuBi8False }));
    }
    // Cover values of field CTRL.SW_APP_ENABLE
    cp_sw_app_read: coverpoint sw_app_enable {
      bins mubi_true  = { MuBi4True };
      bins mubi_false = { MuBi4False };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi4True, MuBi4False }));
    }
    // Cover values of field CTRL.READ_INT_STATE
    cp_read_int_state: coverpoint read_int_state {
      bins mubi_true  = { MuBi4True };
      bins mubi_false = { MuBi4False };
      bins mubi_inval = { [0:$] } with (!(item inside { MuBi4True, MuBi4False }));
    }
    // Cover a scenario where INT_STATE_VAL register is read with a combination of
    // CTRL.READ_INT_STATE field and OTP_EN_CS_SW_APP_READ pin values
    cross_read_int_state_x_otp_en_cs_sw_app_read: cross cp_read_int_state,
                                             cp_otp_en_cs_sw_app_read iff (read_int_state_val_reg);

    // Cover a scenario where GENBITS register is read with a combination of
    // CTRL.SW_APP_ENABLE field and OTP_EN_CS_SW_APP_READ pin values
    cross_sw_app_enable_x_otp_en_cs_sw_app_read: cross cp_sw_app_read, cp_otp_en_cs_sw_app_read
                                                    iff(read_genbits_reg);
  endgroup

  covergroup csrng_genbits_cg with function sample(bit genbits_fips, bit genbits_valid);
    option.per_instance  = 1;
    option.name          = "csrng_genbits_cg";
    // Coverpoint for indicating FIPS/CC compliant bits on genbits register
    genbits_fips_cp: coverpoint genbits_fips iff (genbits_valid) {
      bins fips_compliant = { 1'b1 };
      bins fips_non_compliant = { 1'b0 };
    }
  endgroup

  `DV_FCOV_INSTANTIATE_CG(csrng_sfifo_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_cmds_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_sts_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_err_code_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_err_code_test_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_recov_alert_sts_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_otp_en_sw_app_read_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_genbits_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(csrng_env_cfg cfg);
    csrng_cfg_cg_inst.sample(cfg.otp_en_cs_sw_app_read,
                             cfg.lc_hw_debug_en,
                             cfg.sw_app_enable,
                             cfg.read_int_state,
                             cfg.regwen,
                             cfg.enable
                            );
  endfunction

  function automatic void cg_cmds_sample(bit [NUM_HW_APPS-1:0] hwapp, csrng_item cs_item);
    csrng_cmds_cg_inst.sample(hwapp,
                              cs_item.acmd,
                              cs_item.clen,
                              cs_item.flags,
                              cs_item.glen
                             );
    csrng_sts_cg_inst.sample();
  endfunction

  function automatic void cg_err_code_sample(bit [31:0] err_code);
    // A single error might cause multiple bits in ERR_CODE to get set. For example, some
    // countermeasures always cause the main FSM to escalate and report an error itself.
    for (int unsigned i = 0; i < 27; i++) begin
      if (err_code[i]) begin
        csrng_err_code_cg_inst.sample(err_code_bit_e'(i), err_code[30:28]);
      end
    end
    csrng_sts_cg_inst.sample();
  endfunction

  function automatic void cg_err_test_sample(bit [4:0] err_test_code);
    csrng_err_code_test_cg_inst.sample(err_code_bit_e'(err_test_code));
  endfunction

  function automatic void cg_recov_alert_sample(bit [31:0] recov_alert);
    csrng_recov_alert_sts_cg_inst.sample(recov_alert_bit_e'($clog2(recov_alert)));
  endfunction

  function automatic void cg_csrng_otp_en_sw_app_read_sample(
    bit read_int_state_val_reg,
    bit read_genbits_reg,
    bit [7:0] otp_en_cs_sw_app_read,
    bit [3:0] read_int_state,
    bit [3:0] sw_app_enable
  );
    csrng_otp_en_sw_app_read_cg_inst.sample(
      read_int_state_val_reg,
      read_genbits_reg,
      otp_en_cs_sw_app_read,
      read_int_state,
      sw_app_enable
    );
  endfunction

  function automatic void cg_csrng_genbits_sample(bit genbits_fips, bit genbits_valid);
    csrng_genbits_cg_inst.sample(genbits_fips, genbits_valid);
  endfunction

endinterface : csrng_cov_if
