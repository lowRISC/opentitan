// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This sequence enables entropy refresh by changing the `entropy_refresh_c` constraint:
// 1). Allow `hash_threshold` to be any random value.
// 2). Allow `hash_cnt_clr` to clear the current hash_cnt.
class kmac_entropy_refresh_vseq extends kmac_app_with_partial_data_vseq;

  `uvm_object_utils(kmac_entropy_refresh_vseq)
  `uvm_object_new

  constraint entropy_refresh_c {
    hash_cnt_clr dist {0 :/ 19, 1 :/ 1};
  }

endclass
