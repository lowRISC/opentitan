// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Token mux error injection test

class lc_ctrl_sec_token_mux_vseq extends lc_ctrl_errors_vseq;

  `uvm_object_utils(lc_ctrl_sec_token_mux_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[50 : 100]};}

  constraint tokem_mux_err_inj_c {err_inj.token_mux_ctrl_redun_err == 1;}

endclass
