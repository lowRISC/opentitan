// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_common_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  constraint delay_to_reset_c {
    delay_to_reset dist {
        [1         :1000]       :/ 5,
        [1001      :100_000]    :/ 1,
        [100_001   :1_000_000]  :/ 1,
        [1_000_001 :10_000_000] :/ 3
    };
  }

  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
