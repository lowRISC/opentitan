// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_common_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans); // inherit from cip_base_vseq.sv
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // by default, apply all init, write, and write-read check (CsrNoExcl) for all registers
    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin

      // I2C oversampled values are updated by design according to setting and pin RX
      csr_excl.add_excl({scope, ".", "val"}, CsrExclCheck);

      // intr_test csr is WO which - it reads back 0s, plus it affects the i2c_state csr
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWrite);

      // fdata csr is WO which - it reads back 0s
      csr_excl.add_excl({scope, ".", "fdata"}, CsrExclWrite);

      // intr_state csr is affected by writes to other csrs
      csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclWriteCheck);
    end

    // hw_reset: resets the DUT and the block abstraction class associated with this sequence.
    // reads all of the registers in the block, via all of the available address maps,
    // comparing the value read with the expected reset value
    if (csr_test_type == "hw_reset") begin
      // specify at least one register with reset capability (resval) for this test
      csr_excl.add_excl({scope, ".", "ctrl.enablehost"}, CsrNoExcl);

      // exclude registers which are not able to verify value after reset
      csr_excl.add_excl({scope, ".", "status"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "rdata"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "fdata"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "fifo_ctrl"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "fifo_status"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "ovrd"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "val"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timing0"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timing1"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timing2"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timing3"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timing4"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "timeout_ctrl"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclInitCheck);
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclInitCheck);
    end

    // bit_bash: write 1's and 0's to every bit of non-RO registers (CsrExclWrite/WriteCheck)
    // making sure that the resulting value matches the mirrored value
    if (csr_test_type == "bit_bash") begin
      // specify at least one RW register for this test
      csr_excl.add_excl({scope, ".", "timing0"}, CsrNoExcl);
    end

    // aliasing: write to specifc non-RO/non-INIT register (CsrExclWrite) and
    // read all registers (CsrExclInit/WriteCheck) then check the specifc register
    // content is updated (matching the mirrored value)
    if (csr_test_type == "aliasing") begin
      // specify at least one RW register for this test
      csr_excl.add_excl({scope, ".", "timing0"}, CsrNoExcl);

      // exclude RO register - not able to write
      csr_excl.add_excl({scope, ".", "status"}, CsrExclAll);
      csr_excl.add_excl({scope, ".", "rdata"}, CsrExclAll);
      csr_excl.add_excl({scope, ".", "fifo_status"}, CsrExclAll);
      csr_excl.add_excl({scope, ".", "val"}, CsrExclAll);
    end

    // fmtrst and rxrst fields in fifo_ctrl are WO - it read back 0s
    csr_excl.add_excl({scope, ".", "fifo_ctrl.*rst"}, CsrExclWrite);

    // read rdata when fifo is empty, dut may return unknown data
    csr_excl.add_excl({scope, ".", "rdata"}, CsrExclCheck);

    // status csr is RO - writing is not permitted
    csr_excl.add_excl({scope, ".", "status"}, CsrExclWrite);

  endfunction : add_csr_exclusions

endclass : i2c_common_vseq
