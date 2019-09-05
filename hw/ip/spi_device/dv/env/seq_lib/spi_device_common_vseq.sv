// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_common_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task pre_start();
    super.pre_start();
    // keep sck on - needed for csr tests since some csrs are flopped on sck
    cfg.m_spi_agent_cfg.sck_on = 1'b1;;
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");
    // write exclusions - these should not apply to hw_reset test
    if (csr_test_type != "hw_reset") begin
      // status reads back unexpected values due to writes to other csrs
      csr_excl.add_excl({scope, ".", "status"}, CsrExclWriteCheck);

      // intr_test csr is WO - read behavior undefined and mismatches with uvm_reg_field
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWriteCheck);

      // intr_state reads back unexpected values due to writes to other csrs
      csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclWriteCheck);

      // hw modifies rptr for the txfifo in unexpected way
      csr_excl.add_excl({scope, ".", "txf_ptr.rptr"}, CsrExclWriteCheck);

      // hw modifies async_fifo_level.txlvl when txf_ptr.wptr is updated
      csr_excl.add_excl({scope, ".", "async_fifo_level.txlvl"}, CsrExclWriteCheck);
    end
  endfunction

endclass
