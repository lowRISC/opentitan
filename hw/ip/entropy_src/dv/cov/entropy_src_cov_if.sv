// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for entropy_src.
interface entropy_src_cov_if
  import entropy_src_pkg::*;
  import prim_mubi_pkg::*;
(
  input logic clk_i,
  mubi8_t     otp_en_entropy_src_fw_read_i,
  mubi8_t     otp_en_entropy_src_fw_over_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import entropy_src_reg_pkg::*;
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
        cp_rng_bit_sel, cp_es_type, cp_otp_en_es_fw_read;

    // Entropy data interface functions despite any changes to the fw_ov settings
    cr_fw_ov: cross cp_fw_ov_mode, cp_entropy_insert;

  endgroup : entropy_src_seed_output_csr_cg;

  // Covergroup to confirm that the CSRNG HW interface works
  // for all configurations
  covergroup entropy_src_csrng_hw_cg with function sample(bit [3:0] fips_enable,
                                                          bit [3:0] threshold_scope,
                                                          bit [3:0] rng_bit_enable,
                                                          bit [1:0] rng_bit_sel,
                                                          bit [3:0] es_route,
                                                          bit [3:0] es_type,
                                                          bit [3:0] entropy_data_reg_enable,
                                                          bit [7:0] otp_en_es_fw_read,
                                                          bit [3:0] fw_ov_mode,
                                                          bit [3:0] entropy_insert);

    option.name         = "entropy_src_csrng_hw_cg";
    option.per_instance = 1;

    // For the purposes of this CG, ignore coverage of invalid MuBi values
    cp_fips_enable: coverpoint fips_enable {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_threshold_scope: coverpoint threshold_scope {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_enable: coverpoint rng_bit_enable {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_sel: coverpoint rng_bit_sel;

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

    // CSRNG HW interface is tested with all valid configurations
    cr_config: cross cp_fips_enable, cp_threshold_scope, cp_rng_bit_enable,
        cp_rng_bit_sel, cp_es_type, cp_otp_en_es_fw_read;

    // CSRNG HW interface functions despite any changes to the fw_ov settings
    cr_fw_ov: cross cp_fw_ov_mode, cp_entropy_insert;

  endgroup : entropy_src_csrng_hw_cg;

  // Covergroup to confirm that the Observe FIFO interface works
  // for all configurations
  covergroup entropy_src_observe_fifo_cg with function sample(mubi4_t   fips_enable,
                                                              mubi4_t   threshold_scope,
                                                              mubi4_t   rng_bit_enable,
                                                              bit [1:0] rng_bit_sel,
                                                              mubi4_t   es_route,
                                                              mubi4_t   es_type,
                                                              mubi4_t   entropy_data_reg_enable,
                                                              mubi8_t   otp_en_es_fw_read,
                                                              mubi4_t   fw_ov_mode,
                                                              mubi4_t   entropy_insert);

    option.name         = "entropy_src_seed_observe_fifo_cg";
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
    cp_threshold_scope: coverpoint threshold_scope {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_enable: coverpoint rng_bit_enable {
      bins        mubi_true  = { MuBi4True };
      bins        mubi_false = { MuBi4False };
    }

    cp_rng_bit_sel: coverpoint rng_bit_sel;

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
    }

    // No data should emerge from the Observe FIFO when disabled
    cp_fw_ov_mode: coverpoint fw_ov_mode {
      bins         mubi_true  = { MuBi4True };
      illegal_bins mubi_false = { MuBi4False };
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

  endgroup : entropy_src_observe_fifo_cg;

  `DV_FCOV_INSTANTIATE_CG(entropy_src_seed_output_csr_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(entropy_src_csrng_hw_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(entropy_src_observe_fifo_cg, en_full_cov)

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

  function automatic void cg_csrng_hw_sample(bit [3:0] fips_enable,
                                             bit [3:0] threshold_scope,
                                             bit [3:0] rng_bit_enable,
                                             bit [1:0] rng_bit_sel,
                                             bit [3:0] es_route,
                                             bit [3:0] es_type,
                                             bit [3:0] entropy_data_reg_enable,
                                             bit [7:0] otp_en_es_fw_read,
                                             bit [3:0] fw_ov_mode,
                                             bit [3:0] entropy_insert);
    entropy_src_csrng_hw_cg_inst.sample(fips_enable, threshold_scope, rng_bit_enable,
                                        rng_bit_sel, es_route, es_type,
                                        entropy_data_reg_enable, otp_en_es_fw_read,
                                        fw_ov_mode, entropy_insert);
  endfunction

  function automatic void cg_observe_fifo_sample(mubi4_t   fips_enable,
                                                 mubi4_t   threshold_scope,
                                                 mubi4_t   rng_bit_enable,
                                                 bit [1:0] rng_bit_sel,
                                                 mubi4_t   es_route,
                                                 mubi4_t   es_type,
                                                 mubi4_t   entropy_data_reg_enable,
                                                 mubi8_t   otp_en_es_fw_read,
                                                 mubi4_t   fw_ov_mode,
                                                 mubi4_t   entropy_insert);
    entropy_src_observe_fifo_cg_inst.sample(fips_enable, threshold_scope, rng_bit_enable,
                                            rng_bit_sel, es_route, es_type,
                                            entropy_data_reg_enable, otp_en_es_fw_read,
                                            fw_ov_mode, entropy_insert);
  endfunction

  logic csrng_if_req, csrng_if_ack;
  mubi4_t fips_enable_csr, threshold_scope_csr, rng_bit_enable_csr, rng_bit_sel_csr, es_route_csr,
          es_type_csr, entropy_data_reg_enable_csr, fw_ov_mode_csr, entropy_insert_csr;
  mubi8_t otp_en_es_fw_read_val;

  assign csrng_if_req = tb.dut.entropy_src_hw_if_i.es_req;
  assign csrng_if_ack = tb.dut.entropy_src_hw_if_o.es_ack;

  always @(posedge clk_i) begin
    if(csrng_if_req && csrng_if_ack) begin
      cg_csrng_hw_sample(tb.dut.reg2hw.conf.fips_enable.q,
                         tb.dut.reg2hw.conf.threshold_scope.q,
                         tb.dut.reg2hw.conf.rng_bit_enable.q,
                         tb.dut.reg2hw.conf.rng_bit_sel.q,
                         tb.dut.reg2hw.entropy_control.es_route.q,
                         tb.dut.reg2hw.entropy_control.es_type.q,
                         tb.dut.reg2hw.conf.entropy_data_reg_enable.q,
                         otp_en_entropy_src_fw_read_i,
                         tb.dut.reg2hw.fw_ov_control.fw_ov_mode.q,
                         tb.dut.reg2hw.fw_ov_control.fw_ov_entropy_insert.q);
    end
  end

endinterface : entropy_src_cov_if
