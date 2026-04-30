// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// For each CSR, this sequence writes a random value to it and reads ALL CSRs back. The read value
// of the CSR that was written is checked for correctness while adhering to its access policies. The
// read value of all other CSRs are compared against their previous values. This verifies that there
// is no aliasing across the address bits within the valid CSR space.

class csr_aliasing_seq extends csr_base_seq;
  `uvm_object_utils(csr_aliasing_seq)

  `uvm_object_new

  virtual task body();
    foreach(test_csrs[i]) begin
      uvm_reg_data_t wdata;

      // check if parent block or register is excluded
      if (is_excl(test_csrs[i], CsrExclWrite, CsrAliasingTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn,
                $sformatf("Verifying register aliasing for %0s (register %0d / %0d)",
                          test_csrs[i].get_full_name(), i + 1, test_csrs.size()),
                UVM_MEDIUM)

      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      wdata = get_csr_wdata_with_write_excl(test_csrs[i], wdata, CsrAliasingTest);
      csr_wr(.ptr(test_csrs[i]), .value(wdata), .blocking(0), .predict(!external_checker));

      all_csrs.shuffle();

      // If all_csrs queue size is larger than 100, randomly pick 100 CSRs to avoid chip level test
      // runtime too long.
      if (all_csrs.size() > 100) all_csrs = all_csrs[0 : 99];

      foreach (all_csrs[j]) begin
        uvm_reg_data_t compare_mask;

        // check if parent block or register is excluded
        if (is_excl(all_csrs[j], CsrExclInitCheck, CsrAliasingTest) ||
            is_excl(all_csrs[j], CsrExclWriteCheck, CsrAliasingTest)) begin
          `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclInit/WriteCheck exclusion",
                                    all_csrs[j].get_full_name()), UVM_HIGH)
          continue;
        end

        compare_mask = get_mask_excl_fields(all_csrs[j], CsrExclWriteCheck, CsrAliasingTest);
        csr_rd_check(.ptr           (all_csrs[j]),
                     .blocking      (0),
                     .compare       (!external_checker),
                     .compare_vs_ral(1'b1),
                     .compare_mask  (compare_mask));
      end
      wait_no_outstanding_access();
    end
  endtask

endclass
