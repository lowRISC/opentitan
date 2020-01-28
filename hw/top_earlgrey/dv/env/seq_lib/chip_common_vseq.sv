// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define add_ip_csr_exclusions(ip) \
  begin \
    ip``_common_vseq m_``ip``_common_vseq; \
    m_``ip``_common_vseq = ip``_common_vseq::type_id::create({"m_", `"ip`", "_common_vseq"}); \
    m_``ip``_common_vseq.add_csr_exclusions(csr_test_type, csr_excl, {scope, ".", `"ip`"}); \
  end

class chip_common_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    `uvm_info(`gfn, $sformatf("%0s", cfg.ral.sprint()), UVM_LOW)
    run_csr_vseq_wrapper(num_trans);
  endtask : body


  // function to add csr exclusions of the given type using the csr_excl_item item
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");

    // reuse exclusions from IP benches
    `add_ip_csr_exclusions(uart)
    `add_ip_csr_exclusions(gpio)
    `add_ip_csr_exclusions(hmac)
    `add_ip_csr_exclusions(rv_timer)
    `add_ip_csr_exclusions(spi_device)

  endfunction

endclass

`undef add_ip_csr_exclusions
