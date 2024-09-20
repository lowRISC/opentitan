// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class rstmgr_sw_rst_cg_wrap;
  covergroup sw_rst_cg(string name) with function sample (bit enable, bit rst_n);
    option.name = name;
    option.per_instance = 1;

    enable_cp: coverpoint enable;
    rst_n_cp: coverpoint rst_n;

    sw_rst_cross: cross enable, rst_n;
  endgroup

  function new(string name);
    sw_rst_cg = new(name);
  endfunction

  function void sample (bit enable, bit rst_n);
    sw_rst_cg.sample(enable, rst_n);
  endfunction
endclass

class rstmgr_env_cov extends cip_base_env_cov #(
  .CFG_T(rstmgr_env_cfg)
);
  `uvm_component_utils(rstmgr_env_cov)

  // the base class provides the following handles for use:
  // rstmgr_env_cfg: cfg

  rstmgr_sw_rst_cg_wrap sw_rst_cg_wrap[NumSwResets];

  covergroup alert_info_capture_cg with function sample (logic [7:0] reset_info, logic enable);
    reset_info_cp: coverpoint reset_info {
      bins reset_info_cp[] = {1, 2, 4, 8, 16, 32, 64, 128};
      bins others = default;
    }
    enable_cp: coverpoint enable;
    capture_cross: cross reset_info_cp, enable_cp;
  endgroup

  covergroup alert_info_access_cg with function sample (logic [3:0] index);
    index_cp: coverpoint index {
      bins valid[] = {[0 : ($bits(alert_crashdump_t) + 31) / 32 - 1]};
      bins others = default;
    }
  endgroup

  covergroup cpu_info_capture_cg with function sample (logic [7:0] reset_info, logic enable);
    reset_info_cp: coverpoint reset_info {
      bins reset_info_cp[] = {1, 2, 4, 8, 16, 32, 64, 128};
      bins others = default;
    }
    enable_cp: coverpoint enable;
    capture_cross: cross reset_info_cp, enable_cp;
  endgroup

  covergroup cpu_info_access_cg with function sample (logic [3:0] index);
    index_cp: coverpoint index {
      bins valid[] = {[0 : ($bits(rv_core_ibex_pkg::cpu_crash_dump_t) + 31) / 32 - 1]};
      bins others = default;
    }
  endgroup

  covergroup reset_stretcher_cg with function sample (byte length, byte count);
    length_cp: coverpoint length {
      bins lb[8] = {[1 : 40]};
      bins others = default;
    }
    count_cp: coverpoint count {
      bins cb[4] = {[0 : 15]};
      bins others = default;
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    foreach (sw_rst_cg_wrap[i]) begin
      string cg_name = $sformatf("sw_rst_ctrl_n[%0d]", i);
      sw_rst_cg_wrap[i] = new(cg_name);
    end
    alert_info_capture_cg = new();
    alert_info_access_cg = new();
    cpu_info_capture_cg = new();
    cpu_info_access_cg = new();
    reset_stretcher_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
