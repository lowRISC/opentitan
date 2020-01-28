// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_common_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_common_vseq)

  constraint num_trans_c {
    num_trans inside {[10:25]};
  }

  `uvm_object_new

  task pre_start();
    super.pre_start();
  endtask : pre_start

  virtual task body();
    // disable i2c_monitor since it can not handle this test
    `uvm_info(`gtn, $sformatf("disable i2c_monitor"), UVM_DEBUG)
    cfg.m_i2c_agent_cfg.en_monitor <= 1'b0;
    run_common_vseq_wrapper(num_trans); // inherit from cip_base_vseq.sv
  endtask : body

  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // by default, apply all init, write, and write-read check (CsrNoExcl) for all registers
    if (csr_test_type != "hw_reset") begin   // csr_rw, csr_bit_bash, or csr_aliasing
      // RO registers - not able to write
      csr_excl.add_excl({scope, ".", "val"}, CsrExclWriteCheck);
      // intr_test csr is WO which - it reads back 0s, plus it affects the i2c_state csr
      csr_excl.add_excl({scope, ".", "intr_test"}, CsrExclWriteCheck);
      // fdata csr is WO which - it reads back 0s
      csr_excl.add_excl({scope, ".", "fdata"}, CsrExclWriteCheck);
      // intr_state csr is affected by writes to other csrs
      csr_excl.add_excl({scope, ".", "intr_state"}, CsrExclWriteCheck);
    end

    // aliasing: write to specifc non-RO/non-INIT register (CsrExclWrite) and
    // read all registers (CsrExclInit/WriteCheck) then check the specifc register
    // content is updated (matching the mirrored value)
    if (csr_test_type == "aliasing") begin
      // RO registers - not able to write
      csr_excl.add_excl({scope, ".", "status"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "rdata"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "fifo_status"}, CsrExclWrite);
      csr_excl.add_excl({scope, ".", "val"}, CsrExclWrite);
    end

    // for csr_rw test
    // fmtrst and rxrst fields in fifo_ctrl are WO - it read back 0s
    csr_excl.add_excl({scope, ".", "fifo_ctrl.*rst"}, CsrExclWriteCheck);
    // read rdata when fifo is empty, dut may return unknown data
    csr_excl.add_excl({scope, ".", "rdata"}, CsrExclWriteCheck);
    // status csr is RO - writing is not permitted
    csr_excl.add_excl({scope, ".", "status"}, CsrExclWrite);

  endfunction : add_csr_exclusions

  task post_start();
    `uvm_info(`gfn, "stop simulation", UVM_DEBUG)
  endtask : post_start

endclass : i2c_common_vseq
