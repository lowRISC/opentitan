// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence reads all CSRs and checks their values against the reset value provided in the RAL
// specification. Note that this does not sufficiently qualify as the CSR HW reset test. The 'full'
// CSR HW reset test is constructed externally by running csr_write_seq first, issuing reset and
// only then running this sequence.

class csr_hw_reset_seq extends csr_base_seq;
  `uvm_object_utils(csr_hw_reset_seq)

  extern function new (string name="");

  // Read all CSRs, expecting their values to match their reset values in the register block.
  extern task body();

  // Read the given CSR if it is not excluded and check its value matches the expected reset value.
  // If the register has an HDL path, use two reads, starting with a backdoor one.
  extern local task test_one_csr(uvm_reg csr);
endclass

function csr_hw_reset_seq::new (string name="");
  super.new(name);
endfunction

task csr_hw_reset_seq::body();
  foreach (test_csrs[i]) begin
    test_one_csr(test_csrs[i]);
  end
endtask

task csr_hw_reset_seq::test_one_csr(uvm_reg csr);
  uvm_reg_data_t compare_mask;

  // check if parent block or register is excluded from init check
  if (is_excl(csr, CsrExclInitCheck, CsrHwResetTest)) begin
    `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclInitCheck exclusion",
                              csr.get_full_name()), UVM_MEDIUM)
    return;
  end

  `uvm_info(`gtn, $sformatf("Verifying reset value of register %0s",
                            csr.get_full_name()), UVM_MEDIUM)

  compare_mask = get_mask_excl_fields(csr, CsrExclInitCheck, CsrHwResetTest);
  // Read CSR twice, one from backdoor (if path available), the other from frontdoor.
  if (csr.has_hdl_path()) begin
    // Reading from backdoor can ensure that we deposit value into the storage rather than just a
    // net. If we mistakenly deposit to a net, reset can't clear it and this check will fail.
    csr_rd_check(.ptr           (csr),
                 .backdoor      (1),
                 .compare       (!external_checker),
                 .compare_vs_ral(1'b1),
                 .compare_mask  (compare_mask));
  end

  // Read and check value via frontdoor.
  csr_rd_check(.ptr           (csr),
               .backdoor      (0),
               .blocking      (0),
               .compare       (!external_checker),
               .compare_vs_ral(1'b1),
               .compare_mask  (compare_mask));
endtask
