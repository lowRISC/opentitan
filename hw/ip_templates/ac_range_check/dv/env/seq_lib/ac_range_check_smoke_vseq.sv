// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_smoke_vseq)

  // Local variables
  rand bit zero_delays;
  rand protected bit [NUM_RANGES-1:0] config_range_mask;  // Which ranges should be constrained

  // Constraints
  extern constraint num_trans_c;
  extern constraint tmp_c;
  extern constraint range_c;
  extern constraint range_attr_c;
  extern constraint range_racl_policy_c;
  extern constraint tl_main_vars_addr_c;
  extern constraint tl_main_vars_mask_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ac_range_check_smoke_vseq


constraint ac_range_check_smoke_vseq::num_trans_c {
  num_trans inside {[50:100]};
}

// TODO remove this temporary directed constraint
constraint ac_range_check_smoke_vseq::tmp_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_attr[i].log_denied_access == 1;
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
    send_single_tl_unfilt_tr(zero_delays);  // Send a single TLUL seq with random zero delays
    $display("\n");
  end
endtask : body
