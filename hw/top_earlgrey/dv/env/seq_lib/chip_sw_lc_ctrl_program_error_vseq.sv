// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Injects an error in the lc program request received by the OTP.
class chip_sw_lc_ctrl_program_error_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_program_error_vseq)

  `uvm_object_new

  virtual task body();
    super.body();

    // Wait for C side to fully stabilize
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Begin life cycle transition");,
             "timeout waiting for C side acknowledgement",
             cfg.sw_test_timeout_ns)

    `DV_SPINWAIT(cfg.chip_vif.create_illegal_lc_request_for_otp();,
                 "timeout waiting for an lc_program request for otp_ctrl",
                 cfg.sw_test_timeout_ns)
  endtask
endclass
