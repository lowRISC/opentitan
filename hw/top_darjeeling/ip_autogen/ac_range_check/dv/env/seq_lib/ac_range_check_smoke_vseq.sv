// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_vseq extends ac_range_check_base_vseq;
  import ac_range_check_reg_pkg::*;
  `uvm_object_utils(ac_range_check_smoke_vseq)

  // Local variables
  rand bit zero_delays;
  rand protected bit [NUM_RANGES-1:0] config_range_mask;  // Which ranges should be constrained
  rand bit log_enable;
  rand bit [DenyCountWidth-1:0] deny_cnt_threshold;
  rand bit intr_enable;

  // Non-randomizable local variables
  bit fixed_log_enable;
  bit [DenyCountWidth-1:0] fixed_deny_cnt_threshold;
  bit fixed_intr_enable;

  // Constraints
  extern constraint num_trans_c;
  extern constraint log_denied_access_c;
  extern constraint range_c;
  extern constraint range_attr_c;
  extern constraint range_racl_policy_c;
  extern constraint tl_main_vars_addr_c;
  extern constraint tl_main_vars_mask_c;
  extern constraint log_enable_c;
  extern constraint deny_cnt_threshold_c;
  extern constraint intr_enable_c;

  // Control flags
  bit apply_log_enable_c;
  bit apply_deny_cnt_threshold_c;
  bit apply_intr_enable_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
  extern task set_logging();
  extern task check_logging();
endclass : ac_range_check_smoke_vseq


constraint ac_range_check_smoke_vseq::num_trans_c {
  num_trans inside {[(2 << DenyCountWidth)+50:(2 << DenyCountWidth)+150]};
}

// Enable deny_access 3/4 of the time for each range
constraint ac_range_check_smoke_vseq::log_denied_access_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_attr[i].log_denied_access dist {
      0 :/ 1,
      1 :/ 3
    };
  }
}

constraint ac_range_check_smoke_vseq::range_c {
  solve config_range_mask before dut_cfg.range_base;
  solve dut_cfg.range_base before dut_cfg.range_limit;
  foreach (dut_cfg.range_limit[i]) {
    // Limit always greater than base
    dut_cfg.range_limit[i] > dut_cfg.range_base[i];
    if (config_range_mask[i]) {
      // Range size in 32-bit words, it shouldn't be too large and let it be 1 word size
      ((dut_cfg.range_limit[i] - dut_cfg.range_base[i]) >> 2) inside {[1:49]};
    }
  }
}

// Enable/allow the range 2/3 of the time, to get more granted accesses
constraint ac_range_check_smoke_vseq::range_attr_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_attr[i].execute_access dist {
      0 :/ 1,
      1 :/ 2
    };
    dut_cfg.range_attr[i].write_access dist {
      0 :/ 1,
      1 :/ 2
    };
    dut_cfg.range_attr[i].read_access dist {
      0 :/ 1,
      1 :/ 2
    };
    dut_cfg.range_attr[i].enable dist {
      0 :/ 1,
      1 :/ 2
    };
  }
}

constraint ac_range_check_smoke_vseq::range_racl_policy_c {
  foreach (dut_cfg.range_racl_policy[i]) {
    soft dut_cfg.range_racl_policy[i].write_perm == 16'hFFFF;
    soft dut_cfg.range_racl_policy[i].read_perm  == 16'hFFFF;
  }
}

constraint ac_range_check_smoke_vseq::tl_main_vars_addr_c {
  solve dut_cfg.range_base before tl_main_vars;
  solve dut_cfg.range_limit before tl_main_vars;
  solve range_idx before tl_main_vars;
  tl_main_vars.addr dist {
    // 98% more or less inside range, this will allow us to also test the range boundaries, as this
    // is usually where bug are found (+/-2*32-bit words -> -8 for the range_base and +4 for the
    // range_limit as range_limit is exclusive)
    [dut_cfg.range_base[range_idx]-8  : dut_cfg.range_limit[range_idx]+4] :/ 98,
    // 1% on the lowest part of the range
    [0                                : 9                               ] :/ 1,
    // 1% on the uppermost part of the range
    [2^NUM_RANGES-10                  : 2^NUM_RANGES-1                  ] :/ 1
  };
}

constraint ac_range_check_smoke_vseq::tl_main_vars_mask_c {
  soft tl_main_vars.mask == 'hF;
}

function ac_range_check_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_smoke_vseq::body();
  set_logging();
  for (int i=1; i<=num_trans; i++) begin
    `uvm_info(`gfn, $sformatf("Starting seq %0d/%0d", i, num_trans), UVM_LOW)

    // Randomly keep the same configuration to allow transactions back to back transactions, as no
    // configuration change will happen in between
    randcase
      // 25% of the time, change the config
      1: begin
        `DV_CHECK_RANDOMIZE_FATAL(this)
        ac_range_check_init();
      end
      // 75% of the time, keep the same config
      3: begin
        `uvm_info(`gfn, $sformatf("Keep the same configuration for seq #%0d", i), UVM_MEDIUM)
      end
    endcase

    randcase
      // Trigger log_clear 10% of the time
      1: begin
        ral.log_config.log_clear.set(1);
        csr_update(.csr(ral.log_config));
      end

      // Other times, leave the configuration as is
      9: begin
        `uvm_info(`gfn, $sformatf("Do not trigger a log_clear for seq #%0d", i), UVM_MEDIUM)
      end
    endcase

    send_single_tl_unfilt_tr(zero_delays);  // Send a single TLUL seq with random zero delays
    $display("\n");
    ral.log_config.log_clear.set(0);
    csr_update(.csr(ral.log_config));
    check_logging();
  end
endtask : body

//====================================
//       LOGGING SEQUENCING
//====================================
constraint ac_range_check_smoke_vseq::log_enable_c {
  if (apply_log_enable_c) {
    log_enable dist {
      0 :/ 3,
      1 :/ 7
    };
  } else {
    log_enable == fixed_log_enable;
  }
}

constraint ac_range_check_smoke_vseq::deny_cnt_threshold_c {
  if (apply_deny_cnt_threshold_c) {
    deny_cnt_threshold dist {
      [8'd0                     : 8'd5]                     :/ 2,
      [8'd6                     : (1 << DenyCountWidth)-7]  :/ 1,
      [(1 << DenyCountWidth)-6  : (1 << DenyCountWidth)-1]  :/ 2
    };
  } else {
    deny_cnt_threshold == fixed_deny_cnt_threshold;
  }
}

constraint ac_range_check_smoke_vseq::intr_enable_c {
  if (apply_intr_enable_c) {
    intr_enable dist {
      0 :/ 1,
      1 :/ 1
    };
  } else {
    intr_enable == fixed_intr_enable;
  }
}

task ac_range_check_smoke_vseq::set_logging();
    apply_log_enable_c         = 1;
    apply_deny_cnt_threshold_c = 1;
    apply_intr_enable_c        = 1;

    // Randomize with constraints enabled for logging
    `DV_CHECK_RANDOMIZE_FATAL(this)
    // Store it
    fixed_deny_cnt_threshold = deny_cnt_threshold;
    fixed_log_enable         = log_enable;
    fixed_intr_enable        = intr_enable;

    // Set logging in CSRs
    ral.log_config.log_enable.set(log_enable);
    ral.log_config.deny_cnt_threshold.set(deny_cnt_threshold);
    csr_update(.csr(ral.log_config));

    // Set interrupt enable
    ral.intr_enable.set(intr_enable);
    csr_update(.csr(ral.intr_enable));

    // Disable constraints for logging
    apply_log_enable_c         = 0;
    apply_deny_cnt_threshold_c = 0;
    apply_intr_enable_c        = 0;
endtask : set_logging

task ac_range_check_smoke_vseq::check_logging();
  uvm_reg_data_t    act_config,
                    act_status,
                    act_address;

  csr_rd(.ptr(ral.log_config), .value(act_config));
  csr_rd(.ptr(ral.log_status), .value(act_status));
  csr_rd(.ptr(ral.log_address), .value(act_address));
endtask : check_logging
