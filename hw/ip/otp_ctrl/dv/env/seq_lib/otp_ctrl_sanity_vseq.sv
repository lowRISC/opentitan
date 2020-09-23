// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class otp_ctrl_sanity_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_sanity_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
  endtask

  task body();
  endtask : body

endclass : otp_ctrl_sanity_vseq

