// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence hook to attach to flash_ctrl_base_vseq.
class flash_ctrl_callback_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_callback_vseq)
  `uvm_object_new

  virtual task apply_reset_callback();
    // Do nothing but can be overridden in closed source environment.
  endtask

  virtual task update_env_mp_info();
    // Do nothing but can be overridden in closed source environment.
  endtask
endclass : flash_ctrl_callback_vseq
