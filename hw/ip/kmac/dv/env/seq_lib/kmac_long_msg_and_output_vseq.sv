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

  // up to 100KB (102,400B) input message
  constraint msg_c {
    msg.size() dist {
      0                   :/ 1,
      [1       : 10_000]  :/ 4,
      [10_001  : 75_000]  :/ 12,
      [75_001  : 100_000] :/ 2,
      [100_001 : 102_400] :/ 1
    };
  }

  // allow full randomization of customization string
  virtual task pre_start();
    custom_str_len_c.constraint_mode(0);
    super.pre_start();
  endtask

endclass
