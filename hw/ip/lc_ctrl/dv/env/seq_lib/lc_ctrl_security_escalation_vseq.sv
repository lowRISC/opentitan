// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Attempt second transition before reset
class lc_ctrl_security_escalation_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_security_escalation_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}
  constraint security_escalation_c {
    err_inj.security_escalation_err == 1;
    security_escalation_err_inj_channels != 0;
    !(security_escalation_err_inj_state inside {EscalateSt, InvalidSt});

    if (security_escalation_err_inj_state inside {PostTransSt, ScrapSt}) {
      security_escalation_err_inj_delay == 0;
    } else
    if (security_escalation_err_inj_state inside {IdleSt}) {
      security_escalation_err_inj_delay inside {[0 : 15]};
    } else {
      security_escalation_err_inj_delay inside {[0 : 3]};
    }
  }

endclass
