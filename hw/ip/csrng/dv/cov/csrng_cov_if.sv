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

  covergroup csrng_cfg_cg with function sample(mubi8_t   otp_en_cs_sw_app_read,
                                               mubi4_t   sw_app_enable,
                                               mubi4_t   read_int_state
                                              );
    option.name         = "csrng_cfg_cg";
    option.per_instance = 1;

    cp_sw_app_read:    coverpoint otp_en_cs_sw_app_read;
    cp_sw_app_enable:  coverpoint sw_app_enable;
    cp_read_int_state: coverpoint read_int_state;

    sw_app_read_sw_app_enable_cross: cross cp_sw_app_read, cp_sw_app_enable;
  endgroup : csrng_cfg_cg

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

  covergroup csrng_internal_cg with function sample(bit[31:0] genbits,
                                                    bit[1:0]  genbits_vld,
                                                    bit[1:0]  sw_cmd_sts,
                                                    bit       regwen,
                                                    bit[3:0]  intr_state,
                                                    bit[3:0]  intr_enable
                                                   );
    option.name         = "csrng_internal_cg";
    option.per_instance = 1;

    // TODO find more efficient way to do this
    cp_genbits0:        coverpoint genbits[0];
    cp_genbits1:        coverpoint genbits[1];
    cp_genbits2:        coverpoint genbits[2];
    cp_genbits3:        coverpoint genbits[3];
    cp_genbits4:        coverpoint genbits[4];
    cp_genbits5:        coverpoint genbits[5];
    cp_genbits6:        coverpoint genbits[6];
    cp_genbits7:        coverpoint genbits[7];
    cp_genbits8:        coverpoint genbits[8];
    cp_genbits9:        coverpoint genbits[9];
    cp_genbits10:       coverpoint genbits[10];
    cp_genbits11:       coverpoint genbits[11];
    cp_genbits12:       coverpoint genbits[12];
    cp_genbits13:       coverpoint genbits[13];
    cp_genbits14:       coverpoint genbits[14];
    cp_genbits15:       coverpoint genbits[15];
    cp_genbits16:       coverpoint genbits[16];
    cp_genbits17:       coverpoint genbits[17];
    cp_genbits18:       coverpoint genbits[18];
    cp_genbits19:       coverpoint genbits[19];
    cp_genbits20:       coverpoint genbits[20];
    cp_genbits21:       coverpoint genbits[21];
    cp_genbits22:       coverpoint genbits[22];
    cp_genbits23:       coverpoint genbits[23];
    cp_genbits24:       coverpoint genbits[24];
    cp_genbits25:       coverpoint genbits[25];
    cp_genbits26:       coverpoint genbits[26];
    cp_genbits27:       coverpoint genbits[27];
    cp_genbits28:       coverpoint genbits[28];
    cp_genbits29:       coverpoint genbits[29];
    cp_genbits30:       coverpoint genbits[30];
    cp_genbits31:       coverpoint genbits[31];

    cp_genbits_vld:     coverpoint genbits_vld;
    cp_sw_cmd_sts:      coverpoint sw_cmd_sts;
    cp_regwen:          coverpoint regwen;
    cp_cs_cmd_req_done: coverpoint {intr_state[0], intr_enable[0]};
    cp_cs_entropy_req:  coverpoint {intr_state[1], intr_enable[1]};
    cp_cs_hw_inst_exc:  coverpoint {intr_state[2], intr_enable[2]};
    cp_cs_fatal_err:    coverpoint {intr_state[3], intr_enable[3]};
  endgroup : csrng_internal_cg

  `DV_FCOV_INSTANTIATE_CG(csrng_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_cmds_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_internal_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(csrng_env_cfg cfg);
    csrng_cfg_cg_inst.sample(cfg.otp_en_cs_sw_app_read,
                              cfg.sw_app_enable,
                              cfg.read_int_state
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

  function automatic void cg_internal_sample(bit[31:0] genbits,
                                             bit[1:0]  genbits_vld,
                                             bit[1:0]  sw_cmd_sts,
                                             bit       regwen,
                                             bit[3:0]  intr_state,
                                             bit[3:0]  intr_enable
                                            );
    csrng_internal_cg_inst.sample(genbits, genbits_vld, sw_cmd_sts, regwen, intr_state,
                                  intr_enable);
  endfunction

endinterface : csrng_cov_if
