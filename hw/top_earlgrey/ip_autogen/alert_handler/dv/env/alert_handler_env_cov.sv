// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_alert_en_regwen_cg_wrap;
  covergroup alert_en_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    alert_en_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    alert_en_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    alert_en_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_alert_class_regwen_cg_wrap;
  covergroup alert_class_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    alert_class_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    alert_class_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    alert_class_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_loc_alert_en_regwen_cg_wrap;
  covergroup loc_alert_en_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    loc_alert_en_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    loc_alert_en_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    loc_alert_en_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_loc_alert_class_regwen_cg_wrap;
  covergroup loc_alert_class_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    loc_alert_class_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    loc_alert_class_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    loc_alert_class_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_ctrl_regwen_cg_wrap;
  covergroup class_ctrl_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    class_ctrl_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    class_ctrl_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    class_ctrl_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_clr_regwen_cg_wrap;
  covergroup class_clr_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    class_clr_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    class_clr_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    class_clr_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_accum_thresh_regwen_cg_wrap;
  covergroup class_accum_thresh_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    class_accum_thresh_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    class_accum_thresh_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    class_accum_thresh_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_timeout_cyc_regwen_cg_wrap;
  covergroup class_timeout_cyc_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    class_timeout_cyc_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    class_timeout_cyc_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    class_timeout_cyc_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_crashdump_trigger_regwen_cg_wrap;
  covergroup class_crashdump_trigger_regwen_cg(string name) with function sample(bit regwen);
    option.name = name;
    class_crashdump_trigger_regwen_cp: coverpoint regwen;
  endgroup

  function new(string name);
    class_crashdump_trigger_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen);
    class_crashdump_trigger_regwen_cg.sample(regwen);
  endfunction
endclass

class alert_handler_class_phase_cyc_regwen_cg_wrap;
  covergroup class_phase_cyc_regwen_cg(string name) with function sample(bit regwen,
                                                                         int phase_index);
    option.name = name;
    class_phase_cyc_regwen_cp: coverpoint regwen;
    phase_index_cp: coverpoint phase_index {
      bins phase_0 = {0};
      bins phase_1 = {1};
      bins phase_2 = {2};
      bins phase_3 = {3};
    }
    regwen_cross_phase: cross class_phase_cyc_regwen_cp, phase_index_cp;
  endgroup

  function new(string name);
    class_phase_cyc_regwen_cg = new(name);
  endfunction

  function void sample(bit regwen, int phase_index);
    class_phase_cyc_regwen_cg.sample(regwen, phase_index);
  endfunction
endclass

class alert_handler_env_cov extends cip_base_env_cov #(.CFG_T(alert_handler_env_cfg));
  `uvm_component_utils(alert_handler_env_cov)

  // covergroups
  covergroup accum_cnt_cg with function sample(int class_index, int cnt);
    class_index_cp: coverpoint class_index {
      bins class_index[NUM_ALERT_CLASSES] = {[0:NUM_ALERT_CLASSES-1]};
    }
    accum_cnt_cp: coverpoint cnt {
      bins accum_cnt[10] = {[0:'hffff]};
      bins saturate_cnt  = {'hffff};
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

  // Regwen related covergroups
  covergroup ping_timeout_cyc_regwen_cg with function sample(bit regwen);
    ping_timeout_cyc_regwen_cp: coverpoint regwen;
  endgroup

  covergroup ping_timer_en_regwen_cg with function sample(bit regwen);
    ping_timer_en_regwen_cp: coverpoint regwen;
  endgroup

  // Covergroup to make sure simulation is long enough to fetch more than five EDN requests.
  covergroup num_edn_reqs_cg with function sample(int num_edn_reqs);
    num_edn_reqs_cp: coverpoint num_edn_reqs {
      bins less_then_five_reqs = {[1:4]};
      bins five_or_more_reqs   = {[5:$]};
    }
  endgroup

  alert_handler_alert_en_regwen_cg_wrap        alert_en_regwen_cg_wrap[NUM_ALERTS];
  alert_handler_alert_class_regwen_cg_wrap     alert_class_regwen_cg_wrap[NUM_ALERTS];
  alert_handler_loc_alert_en_regwen_cg_wrap    loc_alert_en_regwen_cg_wrap[NUM_LOCAL_ALERTS];
  alert_handler_loc_alert_class_regwen_cg_wrap loc_alert_class_regwen_cg_wrap[NUM_LOCAL_ALERTS];
  alert_handler_class_ctrl_regwen_cg_wrap      class_ctrl_regwen_cg_wrap[NUM_ALERT_CLASSES];
  alert_handler_class_clr_regwen_cg_wrap       class_clr_regwen_cg_wrap[NUM_ALERT_CLASSES];
  alert_handler_class_accum_thresh_regwen_cg_wrap
      class_accum_thresh_regwen_cg_wrap[NUM_ALERT_CLASSES];
  alert_handler_class_timeout_cyc_regwen_cg_wrap
      class_timeout_cyc_regwen_cg_wrap[NUM_ALERT_CLASSES];
  alert_handler_class_crashdump_trigger_regwen_cg_wrap
      class_crashdump_trigger_regwen_cg_wrap[NUM_ALERT_CLASSES];
  alert_handler_class_phase_cyc_regwen_cg_wrap class_phase_cyc_regwen_cg_wrap[NUM_ALERT_CLASSES];

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

    ping_timeout_cyc_regwen_cg = new();
    ping_timer_en_regwen_cg = new();

    num_edn_reqs_cg = new();

    for (int i = 0; i < NUM_ALERTS; i++) begin
      alert_en_regwen_cg_wrap[i] = new($sformatf("alert_en_regwen_cg_wrap[%0d]", i));
      alert_class_regwen_cg_wrap[i] = new($sformatf("alert_class_regwen_cg_wrap[%0d]", i));
    end
    for (int i = 0; i < NUM_LOCAL_ALERTS; i++) begin
      loc_alert_en_regwen_cg_wrap[i] = new($sformatf("loc_alert_en_regwen_cg_wrap[%0d]", i));
      loc_alert_class_regwen_cg_wrap[i] = new($sformatf("loc_alert_class_regwen_cg_wrap[%0d]", i));
    end
    for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
      class_ctrl_regwen_cg_wrap[i] = new($sformatf("class_ctrl_regwen_cg_wrap[%0d]", i));
      class_clr_regwen_cg_wrap[i] = new($sformatf("class_clr_regwen_cg_wrap[%0d]", i));
      class_accum_thresh_regwen_cg_wrap[i] =
          new($sformatf("class_accum_thresh_regwen_cg_wrap[%0d]", i));
      class_timeout_cyc_regwen_cg_wrap[i] =
          new($sformatf("class_timeout_cyc_regwen_cg_wrap[%0d]", i));
      class_crashdump_trigger_regwen_cg_wrap[i] =
          new($sformatf("class_crashdump_trigger_regwen_cg_wrap[%0d]", i));
      class_phase_cyc_regwen_cg_wrap[i] = new($sformatf("class_phase_cyc_regwen_cg_wrap[%0d]", i));
    end
  endfunction : new

endclass
