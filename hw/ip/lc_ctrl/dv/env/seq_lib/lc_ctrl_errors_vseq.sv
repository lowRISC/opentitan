// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates lc transition failures such as token mismatch.
class lc_ctrl_errors_vseq extends lc_ctrl_smoke_vseq;
  `uvm_object_utils(lc_ctrl_errors_vseq)

  `uvm_object_new

  function void pre_randomize();
    this.token_mismatch_err_c.constraint_mode(0);
  endfunction

endclass
