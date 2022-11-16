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

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup csrng_cfg_cg with function sample(bit [7:0] otp_en_cs_sw_app_read,
                                               bit [3:0] lc_hw_debug_en,
                                               mubi4_t   sw_app_enable,
                                               mubi4_t   read_int_state,
                                               bit       regwen
                                              );
    option.name         = "csrng_cfg_cg";
    option.per_instance = 1;

    cp_sw_app_read:    coverpoint otp_en_cs_sw_app_read {
      bins mubi_true  = { MuBi8True };
      bins mubi_false = { MuBi8False };
      bins mubi_inval = {[0:$]} with (!(item inside {MuBi8True, MuBi8False}));
    }
    cp_lc_hw_debug_en: coverpoint lc_hw_debug_en {
      bins lc_on    = { lc_ctrl_pkg::On };
      bins lc_off   = { lc_ctrl_pkg::Off };
      bins lc_inval = {[0:$]} with (!(item inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off}));
    }
    cp_sw_app_enable:  coverpoint sw_app_enable;
    cp_read_int_state: coverpoint read_int_state;
    cp_regwen:         coverpoint regwen;

    sw_app_read_sw_app_enable_cross: cross cp_sw_app_read, cp_sw_app_enable;
  endgroup : csrng_cfg_cg

  covergroup csrng_err_code_cg with function sample(err_code_bit_e err_code);
    option.name         = "csrng_err_code_cg";
    option.per_instance = 1;

    cp_hw_inst_exc: coverpoint u_reg.hw_exc_sts_qs[NUM_HW_APPS-1:0];
    cp_sw_cmd_sts_cmd_rdy: coverpoint u_reg.sw_cmd_sts_cmd_rdy_qs;
    cp_sw_cmd_sts_cmd_sts: coverpoint u_reg.sw_cmd_sts_cmd_sts_qs;
    cp_err_codes: coverpoint err_code;

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

  covergroup csrng_cmds_cg with function sample(bit[NUM_HW_APPS-1:0]   app,
                                                acmd_e                 acmd,
                                                bit[3:0]               clen,
                                                bit[3:0]               flags,
                                                bit[18:0]              glen
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
      illegal_bins illegal = { INV, GENB, GENU };
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
      bins false         = { MuBi4False };
      bins true          = { MuBi4True };
    }

    cp_glen: coverpoint glen {
      bins one         = { 1 };
      bins multiple    = { [2:$] };
      ignore_bins zero = { 0 };
    }

    app_acmd_cross: cross cp_app, cp_acmd;

    acmd_clen_cross: cross cp_acmd, cp_clen {
      ignore_bins invalid = binsof(cp_acmd) intersect { UNI } &&
                            binsof(cp_clen) intersect { [1:$] };
    }

    acmd_flags_cross: cross cp_acmd, cp_flags;
    acmd_glen_cross:  cross cp_acmd, cp_glen;
    flags_clen_acmd_cross:  cross cp_acmd, cp_flags, cp_clen {
      // Use only Entropy Source seed
      bins ins_only_entropy_src_seed = binsof(cp_flags) intersect {MuBi4False} &&
                                       binsof(cp_clen) intersect {0} &&
                                       binsof(cp_acmd) intersect {INS};
      bins res_only_entropy_src_seed = binsof(cp_flags) intersect {MuBi4False} &&
                                       binsof(cp_clen) intersect {0} &&
                                       binsof(cp_acmd) intersect {RES};
      // Use Entropy Source Seed ^ Additional Data (clen)
      bins ins_xored_entropy_src_seed = binsof(cp_flags) intersect {MuBi4False} &&
                                        binsof(cp_clen) intersect {[1:$]} &&
                                        binsof(cp_acmd) intersect {INS};
      bins res_xored_entropy_src_seed = binsof(cp_flags) intersect {MuBi4False} &&
                                        binsof(cp_clen) intersect {[1:$]} &&
                                        binsof(cp_acmd) intersect {RES};
      // Use zero as seed
      bins ins_zero_seed = binsof(cp_flags) intersect {MuBi4True} &&
                           binsof(cp_clen) intersect {0} &&
                           binsof(cp_acmd) intersect {INS};
      bins res_zero_seed = binsof(cp_flags) intersect {MuBi4True} &&
                           binsof(cp_clen) intersect {0} &&
                           binsof(cp_acmd) intersect {RES};
      // Use Additional Data (clen) as seed
      bins ins_add_data_seed = binsof(cp_flags) intersect {MuBi4True} &&
                               binsof(cp_clen) intersect {[1:$]} &&
                               binsof(cp_acmd) intersect {INS};
      bins res_add_data_seed = binsof(cp_flags) intersect {MuBi4True} &&
                               binsof(cp_clen) intersect {[1:$]} &&
                               binsof(cp_acmd) intersect {RES};
      // Since other modes are not related with flag0, ignore them in this cross.
      ignore_bins ignore = binsof(cp_acmd) intersect {UPD, UNI, GEN};
    }
  endgroup : csrng_cmds_cg

  `DV_FCOV_INSTANTIATE_CG(csrng_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_cmds_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_err_code_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_err_code_test_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_recov_alert_sts_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(csrng_env_cfg cfg);
    csrng_cfg_cg_inst.sample(cfg.otp_en_cs_sw_app_read,
                              cfg.lc_hw_debug_en,
                              cfg.sw_app_enable,
                              cfg.read_int_state,
                              cfg.regwen
                             );
  endfunction

  function automatic void cg_cmds_sample(bit[NUM_HW_APPS-1:0] hwapp, csrng_item cs_item);
    csrng_cmds_cg_inst.sample(hwapp,
                              cs_item.acmd,
                              cs_item.clen,
                              cs_item.flags,
                              cs_item.glen
                             );
  endfunction

  function automatic void cg_err_code_sample(bit [31:0] err_code);
    // A single error might cause multiple bits in ERR_CODE to get set. For example, some
    // countermeasures always cause the main FSM to escalate and report an error itself.
    for (int unsigned i = 0; i < 32; i++) begin
      if (err_code[i]) begin
        csrng_err_code_cg_inst.sample(err_code_bit_e'(i));
      end
    end
  endfunction

  function automatic void cg_err_test_sample(bit [4:0] err_test_code);
    csrng_err_code_test_cg_inst.sample(err_code_bit_e'(err_test_code));
  endfunction

  function automatic void cg_recov_alert_sample(bit [31:0] recov_alert);
    csrng_recov_alert_sts_cg_inst.sample(recov_alert_bit_e'($clog2(recov_alert)));
  endfunction

endinterface : csrng_cov_if
