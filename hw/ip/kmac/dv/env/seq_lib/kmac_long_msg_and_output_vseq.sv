// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// long msg and output test
class kmac_long_msg_and_output_vseq extends kmac_smoke_vseq;

  `uvm_object_utils(kmac_long_msg_and_output_vseq)
  `uvm_object_new

  // up to 1KB (1024B) output
  constraint output_len_c {
    output_len dist {
      [1                     : keccak_block_size] :/ 1, // will not require manual squeezing
      [keccak_block_size + 1 : 512]               :/ 2,
      [513                   : 768]               :/ 5,
      [769                   : 1024]              :/ 2
    };
  }

  // keep the max msg size at 10KB to avoid major performance issues
  constraint msg_c {
    msg.size() dist {
      0               :/ 1,
      [1    : 2500]   :/ 1,
      [2501 : 5000]   :/ 1,
      [5001 : 7500]   :/ 3,
      [5001 : 10_000] :/ 4
    };
  }

  // allow full randomization of customization string
  virtual task pre_start();
    custom_str_len_c.constraint_mode(0);
    super.pre_start();
  endtask

endclass
