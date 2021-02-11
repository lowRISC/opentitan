// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sideload test
class kmac_sideload_vseq extends kmac_long_msg_and_output_vseq;

  `uvm_object_utils(kmac_sideload_vseq)
  `uvm_object_new

  // We want a shorter message than the base long_msg test,
  // but still somewhat long
  constraint msg_c {
    msg.size() inside {[0 : 1000]};
  }

  constraint en_sideload_c {
    en_sideload == 1;
  }

endclass
