// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// csr reset and read/write test vseq
class usbdev_csr_test_vseq extends usbdev_common_vseq;
  `uvm_object_utils(usbdev_csr_test_vseq)

  `uvm_object_new

  task body();
    run_csr_vseq_wrapper(.num_times(num_trans), .models({ral}));
  endtask : body

endclass //: usbdev_csr_test_vseq
