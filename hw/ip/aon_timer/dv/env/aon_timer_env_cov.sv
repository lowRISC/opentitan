// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class aon_timer_env_cov extends cip_base_env_cov #(.CFG_T(aon_timer_env_cfg));
  `uvm_component_utils(aon_timer_env_cov)

  // the base class provides the following handles for use:
  // aon_timer_env_cfg: cfg

  // covergroups

  // Covergroup: timer_cfg_cg
  // timer config covergroup definition
  covergroup timer_cfg_cg(string name) with function sample(bit [11:0] prescale,
                                                            bit [31:0] bark_thold,
                                                            bit [31:0] bite_thold,
                                                            bit [31:0] wkup_thold,
                                                            bit wdog_regwen,
                                                            bit pause_in_sleep,
                                                            bit wkup_cause);
    prescale_cp: coverpoint prescale {
      bins prescale_0 = {0};
      bins prescale_1 = {1};
      bins prescale_2_512 = {[2:512]};
      bins prescale_513_1024 = {[513:1024]};
      bins prescale_1025_4096 = {[1025:4096]};
    }
    bark_thold_cp: coverpoint bark_thold {
      bins bark_0 = {0};
      bins bark_1_512 = {[1:512]};
      bins bark_513_1024 = {[513:1024]};
      bins bark_1025_4096 = {[1025:4096]};
      bins bark_max = {'1};
      bins bark_remainder = default;
    }
    bite_thold_cp: coverpoint bite_thold {
      bins bite_0 = {0};
      bins bite_1_512 = {[1:512]};
      bins bite_513_1024 = {[513:1024]};
      bins bite_1025_4096 = {[1025:4096]};
      bins bite_max = {'1};
      bins bite_remainder = default;
    }
    cp_wkup_thold_cp: coverpoint wkup_thold {
      bins wkup_0 = {0};
      bins wkup_1_512 = {[1:512]};
      bins wkup_513_1024 = {[513:1024]};
      bins wkup_1025_4096 = {[1025:4096]};
      bins wkup_max = {'1};
      bins wkup_remainder = default;
    }

    wkup_cause_cp: coverpoint wkup_cause {
      bins wkup_cause_cleared = {0};
    }

    wdog_regwen_cp: coverpoint wdog_regwen;
    pause_in_sleep_cp: coverpoint pause_in_sleep;

  endgroup : timer_cfg_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // [instantiate covergroups here]
    timer_cfg_cg = new(name);
  endfunction : new

endclass
