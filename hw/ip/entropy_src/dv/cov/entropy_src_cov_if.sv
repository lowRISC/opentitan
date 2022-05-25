// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for entropy_src.
interface entropy_src_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import prim_mubi_pkg::*;
  import entropy_src_pkg::*;
  import entropy_src_env_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  // Covergroup to confirm that the entropy_data CSR interface works
  // for all configurations
  covergroup entropy_src_seed_output_csr_cg with function sample(mubi4_t   fips_enable,
                                                                 mubi4_t   threshold_scope,
                                                                 mubi4_t   rng_bit_enable,
                                                                 bit [1:0] rng_bit_sel,
                                                                 mubi4_t   es_route,
                                                                 mubi4_t   es_type,
                                                                 mubi4_t   entropy_data_reg_enable,
                                                                 mubi8_t   otp_en_es_fw_read,
                                                                 mubi4_t   fw_ov_mode,
                                                                 mubi4_t   entropy_insert,
                                                                 bit       full_seed);

    option.name         = "entropy_src_seed_output_csr_cg";
    option.per_instance = 1;

    // For the purposes of this CG, ignore coverage of invalid MuBi values
    cp_fips_enable: coverpoint fips_enable iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_threshold_scope: coverpoint threshold_scope iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_enable: coverpoint rng_bit_enable iff(full_seed) {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_sel: coverpoint rng_bit_sel iff(full_seed);

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

    // Signal an error if data is observed when otp_en_es_fw_read is false.
    // Sample this even if we don't have a full seed, to detect partial seed
    // leakage.
    cp_otp_en_es_fw_read: coverpoint otp_en_es_fw_read {
      bins         mubi_true  = { MuBi8True };
      illegal_bins mubi_false = { MuBi8False };
    }

    // Sample the FW_OV parameters, just to be sure that they
    // don't interfere with the entropy_data interface.
    cp_fw_ov_mode: coverpoint fw_ov_mode {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_entropy_insert: coverpoint entropy_insert {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    // Cross coverage points

    // Entropy data interface is tested with all valid configurations
    cr_config: cross cp_fips_enable, cp_threshold_scope, cp_rng_bit_enable,
        cp_rng_bit_sel, cp_es_type;

    // Entropy data interface functions despite any changes to the fw_ov settings
    cr_fw_ov: cross cp_fw_ov_mode, cp_entropy_insert;

  endgroup : entropy_src_seed_output_csr_cg;

  `DV_FCOV_INSTANTIATE_CG(entropy_src_seed_output_csr_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_seed_output_csr_sample(mubi4_t   fips_enable,
                                                    mubi4_t   threshold_scope,
                                                    mubi4_t   rng_bit_enable,
                                                    bit [1:0] rng_bit_sel,
                                                    mubi4_t   es_route,
                                                    mubi4_t   es_type,
                                                    mubi4_t   entropy_data_reg_enable,
                                                    mubi8_t   otp_en_es_fw_read,
                                                    mubi4_t   fw_ov_mode,
                                                    mubi4_t   entropy_insert,
                                                    bit       full_seed);
    entropy_src_seed_output_csr_cg_inst.sample(fips_enable, threshold_scope, rng_bit_enable,
                                               rng_bit_sel, es_route, es_type,
                                               entropy_data_reg_enable, otp_en_es_fw_read,
                                               fw_ov_mode, entropy_insert, full_seed);
  endfunction

endinterface : entropy_src_cov_if
