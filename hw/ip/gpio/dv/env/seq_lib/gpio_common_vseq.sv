// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_common_vseq extends gpio_base_vseq;
  `uvm_object_utils(gpio_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task dut_init(string reset_kind = "HARD");
    // Implement gpio pulldown for csr tests for avoiding comparison
    // mismatch for DATA_IN register checks
    set_gpio_pulls(.pu(1'b0), .pd(1'b1));
    super.dut_init(reset_kind);
  endtask: dut_init

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");
    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin
      // read value of masked_* registers yield a different value than written
      csr_excl.add_excl({scope, ".", "masked*"}, CsrExclWriteCheck);

      // intr_test csr is WO which - it reads back 0s
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWrite);

      // intr_state csr is affected by writes to other csrs
      csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclWriteCheck);

      if (csr_test_type == "rw") begin
        // avoid writing to masked_out* registers as they affect direct_out value
        // avoid writing to masked_oe* registers as they affect direct_oe value
        csr_excl.add_excl({scope, ".", "masked*"}, CsrExclWrite);

        // data_in is ro register, so exclude its readback check
        csr_excl.add_excl({scope, ".", "data_in"}, CsrExclWriteCheck);
      end
    end

    // writes to specific csr can affect other csrs in aliasing tests
    if (csr_test_type == "aliasing") begin
      csr_excl.add_excl({scope, ".", "direct_o*"}, CsrExclWriteCheck);
      csr_excl.add_excl({scope, ".", "data_in"}, CsrExclWriteCheck);
    end
  endfunction

endclass
