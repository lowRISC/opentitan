// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_env_cov extends cip_base_env_cov #(.CFG_T(alert_handler_env_cfg));
  `uvm_component_utils(alert_handler_env_cov)

  // the base class provides the following handles for use:
  // alert_handler_env_cfg: cfg

  // covergroups
  covergroup accum_cnt_cg with function sample(int class_i, int cnt);
    class_index_cp: coverpoint class_i {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
    accum_cnt_cp: coverpoint cnt {
      bins accum_cnt[20] = {[0:'hffff]};
      bins saturate_cnt  = {'hffff};
    }
    class_cnt_cross: cross class_index_cp, accum_cnt_cp;
  endgroup : accum_cnt_cg

  covergroup esc_sig_length_cg with function sample(int sig_index, int sig_len);
    esc_sig_index: coverpoint sig_index {
      bins index[NUM_ESC_SIGNALS] = {[0:NUM_ESC_SIGNALS-1]};
    }
    esc_sig_len: coverpoint sig_len {
      bins len_2 = {2};
      bins lens_less_than_1000[20] = {[3:1000]};
    }
    len_per_esc_sig: cross esc_sig_index, esc_sig_len;
  endgroup : esc_sig_length_cg

  covergroup alert_cause_cg with function sample(int alert_index, int class_index);
    alert_cause_cp: coverpoint alert_index {
      bins alert[NUM_ALERTS] = {[0:NUM_ALERTS-1]};
      illegal_bins il = default;
    }
    class_i_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    alert_cause_cross_class_index: cross alert_cause_cp, class_i_cp;
  endgroup

  covergroup alert_loc_alert_cause_cg with function sample(local_alert_type_e local_alert,
                                                           int alert_index,
                                                           int class_index);
    loc_alert_cause_cp: coverpoint local_alert {
      bins alert_ping_fail = {LocalAlertPingFail};
      bins alert_integrity_fail = {LocalAlertIntFail};
      illegal_bins il = default;
    }
    alert_i_cp: coverpoint alert_index {
      bins alert[NUM_ALERTS] = {[0:NUM_ALERTS-1]};
      illegal_bins il = default;
    }
    class_i_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    loc_alert_cause_cross_alert_index: cross loc_alert_cause_cp, alert_i_cp;
    loc_alert_cause_cross_class_index: cross loc_alert_cause_cp, class_i_cp;
  endgroup

  covergroup esc_loc_alert_cause_cg with function sample(local_alert_type_e local_alert,
                                                         int esc_index,
                                                         int class_index);
    loc_alert_cause_cp: coverpoint local_alert {
      bins esc_ping_fail = {LocalEscPingFail};
      bins esc_integrity_fail = {LocalEscIntFail};
      illegal_bins il = default;
    }
    esc_i_cp: coverpoint esc_index {
      bins alert[NUM_ESCS] = {[0:NUM_ESCS-1]};
      illegal_bins il = default;
    }
    class_i_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    loc_alert_cause_cross_alert_index: cross loc_alert_cause_cp, esc_i_cp;
    loc_alert_cause_cross_class_index: cross loc_alert_cause_cp, class_i_cp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    accum_cnt_cg = new();
    esc_sig_length_cg = new();
    alert_cause_cg = new();
    alert_loc_alert_cause_cg = new();
    esc_loc_alert_cause_cg = new();
  endfunction : new

endclass
