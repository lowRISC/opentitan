// Copyright lowRISC contributors (OpenTitan project).
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
                                                            bit [63:0] wkup_thold,
                                                            bit wdog_regwen,
                                                            bit pause_in_sleep,
                                                            bit wkup_cause);
    prescale_cp: coverpoint prescale {
      bins prescale_0 = {0};
      bins prescale[32] = {[1:$]};
      bins prescale_max = {'1};
    }
    bark_thold_cp: coverpoint bark_thold {
      bins bark_0 = {0};
      bins bark[32] = {[1:$]};
      bins bark_max = {'1};
    }
    bite_thold_cp: coverpoint bite_thold {
      bins bite_0 = {0};
      bins bite[32] = {[1:$]};
      bins bite_max = {'1};
    }
    wkup_thold_cp: coverpoint wkup_thold {
      bins wkup_0 = {0};
      bins wkup[64] = {[1:$]};
      bins wkup_max = {'1};
    }

    wkup_cause_cp: coverpoint wkup_cause {
      bins wkup_cause_cleared = {0};
    }

    wdog_regwen_cp: coverpoint wdog_regwen;
    pause_in_sleep_cp: coverpoint pause_in_sleep;

  endgroup : timer_cfg_cg

  // Covergroup: wake_up_timer_thold_hit_cg
  // Samples count, threshold and interrupt for the wake-up timer.
  // Crosses the threshold with the interrupt
  covergroup wake_up_timer_thold_hit_cg with function sample(bit        wkup_int,
                                                             bit [63:0] wkup_thold,
                                                             bit [63:0] wkup_count);

    wkup_count_cp: coverpoint wkup_count {
      bins min_val    = {0};
      bins middle_val = {[1:(2**64-2)]};
      bins max_val    = {2**64-1};
    }
    wkup_thold_cp: coverpoint wkup_thold {
      bins min_val    = {0};
      bins middle_val = {[1:(2**64-2)]};
      bins max_val    = {2**64-1};
    }
    wkup_int_cp  : coverpoint wkup_int   {bins unset          = {0};
                                          bins set            = {1};
    }
    wkup_thold_cpXwkup_int_cp:  cross wkup_thold_cp, wkup_int_cp;
  endgroup : wake_up_timer_thold_hit_cg

  // Covergroup: watchdog_timer_bite_thold_hit_cg
  // Samples count, threshold and interrupt for bite interrupt.
  // Crosses the threshold with the interrupt
  covergroup watchdog_timer_bite_thold_hit_cg with function sample(bit        wdog_bite_rst,
                                                                   bit [31:0] wdog_thold,
                                                                   bit [31:0] wdog_count);

    wdog_count_cp:    coverpoint wdog_count {
      bins min_val    = {0};
      bins middle_val = {[1:(2**32-2)]};
      bins max_val    = {2**32-1};
    }
    wdog_thold_cp:    coverpoint wdog_thold {
      bins min_val    = {0};
      bins middle_val = {[1:(2**32-2)]};
      bins max_val    = {2**32-1};
    }
    wdog_bite_rst_cp: coverpoint wdog_bite_rst   { bins unset    = {0};
                                                   bins set      = {1};
    }
    wdog_thold_cpXwdog_bite_rst:  cross wdog_thold_cp, wdog_bite_rst;
  endgroup : watchdog_timer_bite_thold_hit_cg

  // Covergroup: watchdog_timer_bark_thold_hit_cg
  // Samples count, threshold and interrupt for bark interrupt.
  // Crosses the threshold with the interrupt
  covergroup watchdog_timer_bark_thold_hit_cg with function sample(bit        wdog_bark_int,
                                                                   bit [31:0] wdog_thold,
                                                                   bit [31:0] wdog_count);

    wdog_count_cp:    coverpoint wdog_count {
      bins min_val    = {0};
      bins middle_val = {[1:(2**32-2)]};
      bins max_val    = {2**32-1};
    }
    wdog_thold_cp:    coverpoint wdog_thold {
      bins min_val    = {0};
      bins middle_val = {[1:(2**32-2)]};
      bins max_val    = {2**32-1};
    }
    wdog_bark_int_cp: coverpoint wdog_bark_int   { bins unset          = {0};
                                                   bins set            = {1};
    }
    wdog_thold_cpXwdog_bark_rst:  cross wdog_thold_cp, wdog_bark_int;
  endgroup : watchdog_timer_bark_thold_hit_cg

  extern function new(string name, uvm_component parent);

endclass : aon_timer_env_cov

function aon_timer_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  // [instantiate covergroups here]
  timer_cfg_cg = new(name);
  wake_up_timer_thold_hit_cg = new();
  watchdog_timer_bite_thold_hit_cg = new();
  watchdog_timer_bark_thold_hit_cg = new();
endfunction : new
