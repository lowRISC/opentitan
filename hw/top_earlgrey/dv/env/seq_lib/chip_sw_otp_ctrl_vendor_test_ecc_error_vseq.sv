// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This virtual sequence checks that ECC errors in the vendor test partition
// don't trigger a fault. The sequence injects single and double bit errors.
// It communicates the address to the C side via backdoor, since this test is
// only feasible in simulation. The C code checks for expected status.

class chip_sw_otp_ctrl_vendor_test_ecc_error_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_otp_ctrl_vendor_test_ecc_error_vseq)

  `uvm_object_new

  virtual task body();
    bit [TL_AW-1:0] address = otp_ctrl_reg_pkg::VendorTestOffset +
        otp_ctrl_reg_pkg::VendorTestSize / 2;
    bit [TL_DW-1:0] otp_value;
    bit [7:0] address_as_bytes[4] = {<<byte{address}};

    super.body();

    // Let SW know the expected partition and address.
    sw_symbol_backdoor_overwrite("kTestAddress", address_as_bytes);

    // Wait for C-side to be ready.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for single fault injection",
             "Timeout waiting for fault injection request.")
    otp_value = cfg.mem_bkdr_util_h[Otp].read32(address);
    // Inject 1 bit error to trigger an ECC correctable error.
    `uvm_info(`gfn, $sformatf("Injecting single bit ECC error at OTP address 0x%x", address),
              UVM_MEDIUM)
    cfg.mem_bkdr_util_h[Otp].inject_errors(address, 1);
    // And wait for C-side for double fault.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for double fault injection",
             "Timeout waiting for fault injection request.")
    // Inject 2 bit error to trigger an ECC uncorrectable error.
    `uvm_info(`gfn, $sformatf("Injecting double bit ECC error at OTP address 0x%x", address),
              UVM_MEDIUM)
    cfg.mem_bkdr_util_h[Otp].inject_errors(address, 2);
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Address done",
             "Timeout waiting for OTP_CTRL being done with this address.")
    // Backdoor write back the original value so the chip can reboot successfully.
    cfg.mem_bkdr_util_h[Otp].write32(address, otp_value);
  endtask

endclass : chip_sw_otp_ctrl_vendor_test_ecc_error_vseq
