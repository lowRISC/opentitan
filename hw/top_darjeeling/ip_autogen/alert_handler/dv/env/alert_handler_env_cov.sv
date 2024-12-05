// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_ping_with_lpg_cg_wrap;
  covergroup alert_ping_with_lpg_cg(string name) with function sample (bit lpg_en);
    option.per_instance = 1;
    option.name         = name;
    lpg_cg: coverpoint lpg_en {
      bins lpg_en  = {1};
      bins lpg_dis = {0};
    }
  endgroup

  function new(string name);
    alert_ping_with_lpg_cg = new(name);
  endfunction
endclass

class alert_handler_env_cov extends cip_base_env_cov #(.CFG_T(alert_handler_env_cfg));
  `uvm_component_utils(alert_handler_env_cov)

  alert_ping_with_lpg_cg_wrap ping_with_lpg_cg_wrap[NUM_ALERTS];

  // covergroups
  covergroup accum_cnt_cg with function sample(int class_index, int cnt);
    class_index_cp: coverpoint class_index {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
    // Due to the limited simulation time, this only collect accum coverage until 2000. For the
    // saturation case, design has assertions to cover that.
    accum_cnt_cp: coverpoint cnt {
      bins accum_cnt_0    = {0};
      bins accum_cnt_10   = {[1:10]};
      bins accum_cnt_50   = {[11:50]};
      bins accum_cnt_100  = {[51:100]};
      bins accum_cnt_1000 = {[101:1000]};
      bins accum_cnt_2000 = {[1001:2000]};
    }
    class_cnt_cross: cross class_index_cp, accum_cnt_cp;
  endgroup : accum_cnt_cg

  covergroup intr_timeout_cnt_cg with function sample(int class_index, int cnt);
    class_index_cp: coverpoint class_index {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
    intr_timeout_cnt_cp: coverpoint cnt {
      bins intr_timeout_cnt[10] = {[0:1000]};
    }
    class_cnt_cross: cross class_index_cp, intr_timeout_cnt_cp;
  endgroup

  covergroup esc_sig_length_cg with function sample(int sig_index, int sig_len);
    esc_sig_index_cp: coverpoint sig_index {
      bins index[NUM_ESC_SIGNALS] = {[0:NUM_ESC_SIGNALS-1]};
    }
    esc_sig_len_cp: coverpoint sig_len {
      bins len_2 = {2};
      bins lens_less_than_1000[10] = {[3:1000]};
    }
    len_per_esc_sig: cross esc_sig_index_cp, esc_sig_len_cp;
  endgroup : esc_sig_length_cg

  covergroup clear_intr_cnt_cg with function sample(int class_index);
    clear_intr_cnt_cp: coverpoint class_index {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
  endgroup

  covergroup clear_esc_cnt_cg with function sample(int class_index);
    clear_esc_cnt_cp: coverpoint class_index {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
  endgroup

  covergroup alert_cause_cg with function sample(int alert_index, int class_index);
    alert_cause_cp: coverpoint alert_index {
      bins alert[NUM_ALERTS] = {[0:NUM_ALERTS-1]};
      illegal_bins il = default;
    }
    class_index_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    alert_cause_cross_class_index: cross alert_cause_cp, class_index_cp;
  endgroup

  covergroup alert_loc_alert_cause_cg with function sample(local_alert_type_e local_alert,
                                                           int alert_index,
                                                           int class_index);
    loc_alert_cause_cp: coverpoint local_alert {
      bins alert_ping_fail = {LocalAlertPingFail};
      bins alert_integrity_fail = {LocalAlertIntFail};
      illegal_bins il = default;
    }
    alert_index_cp: coverpoint alert_index {
      bins alert[NUM_ALERTS] = {[0:NUM_ALERTS-1]};
      illegal_bins il = default;
    }
    class_index_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    loc_alert_cause_cross_alert_index: cross loc_alert_cause_cp, alert_index_cp;
    loc_alert_cause_cross_class_index: cross loc_alert_cause_cp, class_index_cp;
  endgroup

  covergroup esc_loc_alert_cause_cg with function sample(local_alert_type_e local_alert,
                                                         int esc_index,
                                                         int class_index);
    loc_alert_cause_cp: coverpoint local_alert {
      bins esc_ping_fail = {LocalEscPingFail};
      bins esc_integrity_fail = {LocalEscIntFail};
      illegal_bins il = default;
    }
    esc_index_cp: coverpoint esc_index {
      bins alert[NUM_ESCS] = {[0:NUM_ESCS-1]};
      illegal_bins il = default;
    }
    class_index_cp: coverpoint class_index {
      bins class_i[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
      illegal_bins il = default;
    }
    loc_alert_cause_cross_alert_index: cross loc_alert_cause_cp, esc_index_cp;
    loc_alert_cause_cross_class_index: cross loc_alert_cause_cp, class_index_cp;
  endgroup

  covergroup crashdump_trigger_cg with function sample(bit [1:0] phase);
    crashdump_trigger_phase_cp: coverpoint phase {
      bins phase_0 = {0};
      bins phase_1 = {1};
      bins phase_2 = {2};
      bins phase_3 = {3};
    }
  endgroup

  // Covergroup to make sure simulation is long enough to fetch more than five EDN requests.
  covergroup num_edn_reqs_cg with function sample(int num_edn_reqs);
    num_edn_reqs_cp: coverpoint num_edn_reqs {
      bins less_than_five_reqs = {[1:4]};
      bins five_or_more_reqs   = {[5:$]};
    }
  endgroup

  covergroup num_checked_pings_cg with function sample (int num_pings);
    num_pings_cp: coverpoint num_pings {
      bins less_than_ten_pings = {[1:9]};
      bins ten_to_twenty_pings = {[10:19]};
      bins more_than_twenty_pings = {[20:$]};
    }
  endgroup

  covergroup cycles_between_pings_cg with function sample (int num_cycles_between_pings);
    num_cycles_cp: coverpoint num_cycles_between_pings{
      bins less_than_5000_cycs = {[1:4_999]};
      bins less_than_100k_cycs = {[5_000:99_999]};
      bins less_than_150k_cycs = {[5_000:149_999]};
      bins less_than_200k_cycs = {[150_000:199_999]};
      bins more_than_200k_cycs = {[200_000:$]};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    accum_cnt_cg = new();
    intr_timeout_cnt_cg = new();
    esc_sig_length_cg = new();
    clear_intr_cnt_cg = new();
    clear_esc_cnt_cg = new();
    alert_cause_cg = new();
    alert_loc_alert_cause_cg = new();
    esc_loc_alert_cause_cg = new();
    crashdump_trigger_cg = new();

    num_edn_reqs_cg = new();
    num_checked_pings_cg = new();
    cycles_between_pings_cg = new();

    foreach (ping_with_lpg_cg_wrap[i]) begin
      ping_with_lpg_cg_wrap[i] = new($sformatf("ping_with_lpg_cg_wrap[%0d]", i));
    end
  endfunction : new

endclass
