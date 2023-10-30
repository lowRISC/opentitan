// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

// covergroup to sample all SW input bits are toggled and gated by regwen
class keymgr_dpe_sw_input_cg_wrap;
  localparam int Width = bus_params_pkg::BUS_DW;
  covergroup keymgr_dpe_sw_input_cg (string name)
      with function sample(bit [Width-1:0] sw_input,
                           bit regwen);
    option.per_instance = 1;
    option.name = name;

    sw_input_cp: coverpoint sw_input {
      option.auto_bin_max = Width;
    }
    regwen_cp: coverpoint regwen;
    sw_input_x_regwen_cr: cross sw_input_cp, regwen_cp;
  endgroup

  function new(string name);
    keymgr_dpe_sw_input_cg = new(name);
  endfunction : new

  function void sample(bit [Width-1:0] sw_input, bit regwen);
    keymgr_dpe_sw_input_cg.sample(sw_input, regwen);
  endfunction : sample
endclass

class keymgr_dpe_env_cov extends cip_base_env_cov #(.CFG_T(keymgr_dpe_env_cfg));
  `uvm_component_utils(keymgr_dpe_env_cov)
  keymgr_dpe_sw_input_cg_wrap sw_input_cg_wrap[string];

  // covergroup for keymgr_dpe state and operation with op_status and CDI sel, sideload destination
  covergroup state_and_op_cg with function sample(keymgr_pkg::keymgr_working_state_e state,
                                                  keymgr_pkg::keymgr_ops_e op,
                                                  keymgr_pkg::keymgr_op_status_e op_status,
                                                  keymgr_cdi_type_e cdi,
                                                  keymgr_pkg::keymgr_key_dest_e dest);
    state_cp:     coverpoint state;
    op_cp:        coverpoint op;
    op_status_cp: coverpoint op_status {
      // only sample when op is done
      ignore_bins illegal = {keymgr_pkg::OpIdle, keymgr_pkg::OpWip};
    }
    cdi_cp:       coverpoint cdi iff (!(op inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable}));
    dest_cp:      coverpoint dest iff (op inside {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut});

    op_x_state_cross:  cross op_cp, cdi_cp, dest_cp, state_cp;
    op_x_status_cross: cross op_cp, cdi_cp, dest_cp, op_status_cp;
  endgroup

  // Covergroup to sample LC disable occurs at all the states or during operations
  covergroup lc_disable_cg with function sample(keymgr_pkg::keymgr_working_state_e state,
                                                keymgr_pkg::keymgr_ops_e op,
                                                bit wip);
    state_cp: coverpoint state;
    op_cp: coverpoint op iff (wip == 1);
    wip_cp: coverpoint wip;

    // state crosses with wip or idle
    state_x_wip_cross: cross state_cp, wip_cp;
    // state crosses with operations
    state_x_op_cross: cross state_cp, op_cp;
  endgroup

  // Covergroup to sample sideload_clear in all the states and followed by all the operations
  covergroup sideload_clear_cg with function sample(bit [2:0] sideload_clear,
                                                    keymgr_pkg::keymgr_working_state_e state,
                                                    keymgr_pkg::keymgr_ops_e op,
                                                    bit aes_sl_avail,
                                                    bit kmac_sl_avail,
                                                    bit otbn_sl_avail,
                                                    bit regwen);
    sideload_clear_cp: coverpoint sideload_clear {
      bins clear_none  = {0};
      bins clear_one[] = {[1:3]};
      bins clear_all   = {[4:$]};
    }
    // the state where sideload_clear occurs
    state_cp:          coverpoint state;
    // the operation followed by sideload_clear
    op_cp:             coverpoint op;
    aes_sl_avail_cp:   coverpoint aes_sl_avail;
    kmac_sl_avail_cp:  coverpoint kmac_sl_avail;
    otbn_sl_avail_cp:  coverpoint otbn_sl_avail;
    regwen_cp:         coverpoint regwen;

    sideload_clear_x_state_op_cross: cross sideload_clear, state, op;
    sideload_clear_x_sl_avail_cross: cross sideload_clear_cp, aes_sl_avail, kmac_sl_avail,
                                           otbn_sl_avail;
    sideload_clear_x_regwen_cross:   cross sideload_clear_cp, regwen_cp;
  endgroup

  covergroup err_code_cg with function sample(keymgr_pkg::keymgr_err_pos_e err_code);
    err_code_cp: coverpoint err_code {
      // this is done in a direct test
      ignore_bins ignore = {keymgr_pkg::ErrShadowUpdate};
      illegal_bins illegal = {keymgr_pkg::ErrLastPos};
    }
  endgroup

  covergroup invalid_hw_input_cg with function sample(
      keymgr_dpe_invalid_hw_input_type_e invalid_hw_input);
    invalid_hw_input_cp: coverpoint invalid_hw_input;
  endgroup

  covergroup fault_status_cg with function sample(keymgr_pkg::keymgr_fault_pos_e fault);
    fault_cp: coverpoint fault {
      // these are done in a direct test
      ignore_bins ignore = {keymgr_pkg::FaultRegIntg, keymgr_pkg::FaultShadow};
      illegal_bins illegal = {keymgr_pkg::FaultLastPos};
    }
  endgroup

  // when async and sync fault both happen, use these 2 CP to enable both orders are covered
  covergroup sync_async_fault_cross_cg with function sample(bit sync_fault_trig_first  = 1,
                                                            bit async_fault_trig_first = 1);
    sync_fault_trig_first_cp: coverpoint sync_fault_trig_first {
      bins sync_first = {1};
    }
    async_fault_trig_first_cp: coverpoint async_fault_trig_first {
      bins async_first = {1};
    }
  endgroup

  // Covergroup to cover small values that TB can actually check EDN request sends correctly, and
  // large values to make sure all bits are toggled
  covergroup reseed_interval_cg with function sample(bit[15:0] reseed_interval);
    reseed_interval_cp: coverpoint reseed_interval {
      bins small_values[5]  = {[50:100]};
      bins large_values[32] = {[100:16'hffff]};
    }
  endgroup

  // Covergroup to sample key version comparion with OpGenSwOut and OpGenHwOut in legal states
  // When comparison is CompareOpGt, it's SW invalid input
  covergroup key_version_compare_cg with function sample(compare_op_e key_version_cmp,
                                                         keymgr_pkg::keymgr_working_state_e state,
                                                         keymgr_pkg::keymgr_ops_e op);
    key_version_cmp_cp: coverpoint key_version_cmp {
      bins legal_values[]  = {CompareOpEq, CompareOpGt, CompareOpLt};
    }
    state_cp: coverpoint state {
      bins legal_states[]  = {keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
                              keymgr_pkg::StOwnerKey};
    }
    op_cp: coverpoint op {
      bins legal_states[]  = {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut};
    }
    key_ver_x_state_x_op_cross: cross key_version_cmp_cp, state_cp, op_cp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);

    state_and_op_cg = new();
    lc_disable_cg = new();
    sideload_clear_cg = new();
    err_code_cg = new();
    invalid_hw_input_cg = new();
    fault_status_cg = new();
    sync_async_fault_cross_cg = new();
    reseed_interval_cg = new();
    key_version_compare_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    foreach (cfg.ral.sealing_sw_binding[i]) begin
      create_sw_input_cg_obj(cfg.ral.sealing_sw_binding[i].get_name());
    end
    foreach (cfg.ral.attest_sw_binding[i]) begin
      create_sw_input_cg_obj(cfg.ral.attest_sw_binding[i].get_name());
    end
    foreach (cfg.ral.salt[i]) begin
      create_sw_input_cg_obj(cfg.ral.salt[i].get_name());
    end
    foreach (cfg.ral.key_version[i]) begin
      create_sw_input_cg_obj(cfg.ral.key_version[i].get_name());
    end

    create_sw_input_cg_obj(cfg.ral.max_creator_key_ver_shadowed.get_name());
    create_sw_input_cg_obj(cfg.ral.max_owner_int_key_ver_shadowed.get_name());
    create_sw_input_cg_obj(cfg.ral.max_owner_key_ver_shadowed.get_name());
    create_sw_input_cg_obj(cfg.ral.start.get_name());
  endfunction

  virtual function void create_sw_input_cg_obj(string name);
    sw_input_cg_wrap[name] = new(name);
  endfunction

endclass
