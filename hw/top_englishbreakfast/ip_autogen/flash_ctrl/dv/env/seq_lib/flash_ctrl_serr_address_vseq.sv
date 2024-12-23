// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed test to check flash_ctrl.single_err_addr
// Each round test insert one single bit error and capture the address from tb.
// At the end of each round, compare the captured value with
// csr read (flash_ctrl.single_err_addr) value.
class flash_ctrl_serr_address_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_serr_address_vseq)
  `uvm_object_new

  virtual task body();
    uvm_reg_data_t addr0, addr1;
    super.body();
    cfg.serr_once = 1;

    repeat(10) begin
      cfg.serr_created = 0;
      super.body();

      // Give some slacks to address is stored.
      #1us;

      csr_rd(.ptr(ral.ecc_single_err_addr[0]), .value(addr0));
      csr_rd(.ptr(ral.ecc_single_err_addr[1]), .value(addr1));

      `DV_CHECK_EQ(addr0, cfg.serr_addr[0])
      `DV_CHECK_EQ(addr1, cfg.serr_addr[1])
    end
  endtask // body
endclass // flash_ctrl_serr_address_vseq
