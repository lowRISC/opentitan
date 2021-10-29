// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class sram_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(sram_ctrl_env_cfg));

  `uvm_component_utils(sram_ctrl_env_cov)

  // the base class provides the following handles for use:
  // sram_ctrl_env_cfg: cfg

  // covergroups

  // cover that all access granularities have been tested for both memory reads and writes
  covergroup subword_access_cg with function sample(bit we, bit [TL_DBW-1:0] mask);
    subword_we: coverpoint we;
    subword_granularity: coverpoint mask {
      bins zero_access        = {'b0};
      bins byte_access        = {'b0001, 'b0010, 'b0100, 'b1000};
      bins halfword_access    = {'b0011, 'b0110, 'b1100};
      bins triple_byte_access = {'b0111, 'b1110};
      bins word_access        = {'b1111};
      illegal_bins ill_access = default;
    }
    subword_access: cross subword_we, subword_granularity;
  endgroup

  // cover that SRAM handles mem accesses during key requests, both reads and writes
  covergroup access_during_key_req_cg with function sample(tlul_pkg::tl_a_op_e opcode);
    access_during_key_req: coverpoint opcode {
      bins write            = {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
      bins read             = {tlul_pkg::Get};
      illegal_bins ill_type = default;
    }
  endgroup

  // covers SRAM receiving a key in Off/On states,
  // with both valid/invalid key seeds.
  covergroup key_seed_valid_cg with function sample(bit in_lc_esc, bit seed_valid);
      key_seed_valid: coverpoint seed_valid;
      escalated: coverpoint in_lc_esc;

      key_seed_valid_cross: cross key_seed_valid, escalated;
  endgroup

  // covers RAW hazards that are detected in the SRAM,
  // specifically, whether these hazards are due to address collisions or not.
  covergroup raw_hazard_cg with function sample(bit addr_collision);
    raw_hazard: coverpoint addr_collision;
  endgroup

  // covers that all combinations of reads/writes can create b2b scenario
  covergroup b2b_access_types_cg with function sample(bit first_write_en, bit second_write_en);
    b2b_access_types: cross first_write_en, second_write_en;
  endgroup

  covergroup lc_escalation_rst_cg with function sample(bit rst_n);
    lc_escalation_rst: coverpoint rst_n;
  endgroup

  // covers various scenarios that enable/disable SRAM executability
  covergroup executable_cg with function sample(logic [3:0] lc_hw_debug_en,
                                                logic [7:0] en_sram_ifetch,
                                                logic [2:0] csr_exec);
    // placeholder comment
    en_sram_ifetch_cp: coverpoint en_sram_ifetch {
      bins sram_ifetch_enable = {prim_mubi_pkg::MuBi8True};
      bins sram_ifetch_valid_disable = {prim_mubi_pkg::MuBi8False};
      bins sram_ifetch_invalid_disable = {
          [0 : prim_mubi_pkg::MuBi8False-1],
          [prim_mubi_pkg::MuBi8False+1 : prim_mubi_pkg::MuBi8True-1],
          [prim_mubi_pkg::MuBi8True+1 : '1]};
    }
    lc_hw_debug_en_cp: coverpoint lc_hw_debug_en {
      bins hw_debug_en_on           = {lc_ctrl_pkg::On};
      bins hw_debug_en_valid_off    = {lc_ctrl_pkg::Off};
      bins hw_debug_en_invalid_off  = {[0 : lc_ctrl_pkg::Off-1],
                                       [lc_ctrl_pkg::Off+1 : lc_ctrl_pkg::On-1],
                                       [lc_ctrl_pkg::On+1 : '1]};
    }
    csr_exec_cp : coverpoint csr_exec {
      bins instr_en = {prim_mubi_pkg::MuBi4True};
      bins instr_valid_dis = {prim_mubi_pkg::MuBi4False};
      bins instr_invalid_dis = {[0 : prim_mubi_pkg::MuBi4False-1],
                                [prim_mubi_pkg::MuBi4False+1 : prim_mubi_pkg::MuBi4True-1],
                                [prim_mubi_pkg::MuBi4True+1 : '1]};
    }
    executable_cross: cross lc_hw_debug_en_cp, en_sram_ifetch_cp, csr_exec_cp {
      bins csr_exec_en = binsof(en_sram_ifetch_cp.sram_ifetch_enable) &&
                         binsof(csr_exec_cp.instr_en) &&
                         binsof(lc_hw_debug_en_cp);

      bins lc_exec_en = binsof(en_sram_ifetch_cp.sram_ifetch_enable) &&
                        binsof(lc_hw_debug_en_cp.hw_debug_en_on) &&
                        binsof(csr_exec_cp);

      bins valid_exec_dis = (binsof(en_sram_ifetch_cp.sram_ifetch_enable) &&
                             binsof(csr_exec_cp.instr_valid_dis)) ||
                            (binsof(en_sram_ifetch_cp.sram_ifetch_valid_disable) &&
                             binsof(lc_hw_debug_en_cp.hw_debug_en_valid_off));

      bins invalid_exec_dis = (binsof(en_sram_ifetch_cp.sram_ifetch_enable) &&
                               binsof(csr_exec_cp.instr_invalid_dis)) ||
                              (binsof(en_sram_ifetch_cp.sram_ifetch_invalid_disable) &&
                               binsof(lc_hw_debug_en_cp.hw_debug_en_invalid_off));
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    subword_access_cg         = new();
    access_during_key_req_cg  = new();
    key_seed_valid_cg         = new();
    raw_hazard_cg             = new();
    b2b_access_types_cg       = new();
    lc_escalation_rst_cg      = new();
    executable_cg             = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
