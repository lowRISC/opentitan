// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_multiple_keys_vseq extends sram_ctrl_smoke_vseq;

  `uvm_object_utils(sram_ctrl_multiple_keys_vseq)
  `uvm_object_new

  // Use 2 as the low end since `num_trans == 1` is the default for the smoke test.
  constraint num_trans_c {
    num_trans dist {
      [2  : 13] :/ 2,
      [14 : 25] :/ 3,
      [25 : 37] :/ 4,
      [38 : 50] :/ 1
    };
  }

endclass
