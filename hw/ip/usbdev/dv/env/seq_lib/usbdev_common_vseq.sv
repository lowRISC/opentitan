// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_common_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  task pre_start();
    // Common test sequences do not need device init.
    do_usbdev_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // Link reset occurs every 3 us. There doesn't seem to be a way to turn that off.
    // It results in the modification of some CSRS which makes the prediction hard.
    // Those are being excluded from checks below.

    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin
      // intr_test CSR affects the intr_state csr. It is already tested in intr_test.
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWrite);

      // Writing ral.avbuffer affects the ral.usbstat.av_depth field.
      csr_excl.add_excl({scope, ".", "avbuffer"}, CsrExclWrite);

      // ral.usbctrl.device_address is reset to 0 if usb is not enabled.
      csr_excl.add_excl({scope, ".", "usbctrl.device_address"}, CsrExclWriteCheck);

      // Prevent usb from being enabled to avoid other unforeseen side effects.
      csr_excl.add_excl({scope, ".", "usbctrl.enable"}, CsrExclWrite);

      // Overriding pwr sense will cause the usbdev to think the link is powered up
      csr_excl.add_excl({scope, ".", "phy_config.override_pwr_sense_en"}, CsrExclWrite);
    end
  endfunction

endclass
