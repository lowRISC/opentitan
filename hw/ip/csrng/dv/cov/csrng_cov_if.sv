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

    cp_otp_en_cs_sw_app_read: coverpoint otp_en_cs_sw_app_read;

    cp_sw_app_enable: coverpoint sw_app_enable;

    cp_read_int_state: coverpoint read_int_state;
  endgroup : csrng_cfg_cg

  covergroup csrng_cmds_cg with function sample(bit[NUM_HW_APPS-1:0]   hwapp,
                                                acmd_e                 acmd,
                                                bit[3:0]               clen,
                                                bit[3:0]               flags,
                                                bit[18:0]              glen
                                               );
    option.name         = "csrng_cmds_cg";
    option.per_instance = 1;

    cp_hwapp: coverpoint hwapp;

    cp_acmd: coverpoint acmd {
      illegal_bins illegal = { csrng_pkg::INV, csrng_pkg::GENB, csrng_pkg::GENU };
    }

    cp_clen: coverpoint clen {
      bins no_additional_data = { 0 };
      bins additional_data    = { [1:12] };
      bins invalid            = { [13:15] };
    }

    cp_flags: coverpoint flags {
      bins zero    = { 0 };
      bins one     = { 1 };
      bins invalid = { [2:15] };
    }

    cp_glen: coverpoint glen {
      bins zero      = { 0 };
      bins non_zero  = { [1:$] };
    }

    cr_hwapp_acmd: cross cp_hwapp, cp_acmd;
    cr_acmd_clen:  cross cp_acmd, cp_clen;
    cr_acmd_flags: cross cp_acmd, cp_flags;
    cr_acmd_glen:  cross cp_acmd, cp_glen;
  endgroup : csrng_cmds_cg

  `DV_FCOV_INSTANTIATE_CG(csrng_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(csrng_cmds_cg, en_full_cov)

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

endinterface : csrng_cov_if
