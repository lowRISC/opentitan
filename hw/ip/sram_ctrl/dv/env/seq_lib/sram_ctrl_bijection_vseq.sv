// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests the bijectivity of the SRAM address remapping.
//
// To do this, use the following stimulus:
//
//  - Write a different value to every address in SRAM memory (using the address, so write 0x0 to
//    address 0x0, write 0x4 to address 0x4, etc...).
//
//  - Read the value back from every address in SRAM memory. As well as any check from the
//    scoreboard, the sequence knows the value it expects to read, so can check the value as well.
//
// The test helps us verify that the SRAM address scrambling does not lead to any address collisions
// (e.g. addresses 0x4 and 0x8 do not both map to the same line in memory). If there are any address
// collisions, then we will read out an incorrect value from memory.
//
// The sequence runs twice, requesting a new scrambling key between the two runs (to check that
// nothing gets broken by switching scrambling key)
class sram_ctrl_bijection_vseq extends sram_ctrl_smoke_vseq;
  `uvm_object_utils(sram_ctrl_bijection_vseq)

  function new (string name="");
    super.new(name);
  endfunction

  virtual task body();
    int unsigned sram_depth = cfg.sram_ctrl_bkdr_util_h.get_depth();

    `uvm_info(get_name(),
              $sformatf("Read-write bijection test with %0d iterations over SRAM with depth %0d.",
                        num_trans, sram_depth),
              UVM_LOW)

    for (int i = 0; i < num_trans; i++) begin
      `uvm_info(get_name(),
                $sformatf("Starting iteration %0d of %0d", i+1, num_trans),
                UVM_LOW)

      // Write the corresponding address to each entry in the SRAM
      for (int j = 0; j < sram_depth; j++) begin
        if (cfg.stop_transaction_generators()) return;
        do_single_write(.addr(j*4), .data(j*4), .mask('1));
      end

      // Read each location back, the read data should be the same as its address
      for (int j = 0; j < sram_depth; j++) begin
        logic [TL_DW-1:0] rdata;
        if (cfg.stop_transaction_generators()) return;
        do_single_read(.addr(j*4), .mask('1), .check_rdata(1),
                       .exp_rdata(j*4), .rdata(rdata));
      end

      // request new scrambling key on all but the last iteration
      if (i != num_trans - 1) begin
        `uvm_info(get_name(), "Rotating scrambling key", UVM_LOW)
        req_scr_key();
      end
    end
  endtask : body

  // Only run two transactions: this will ensure we check a new scrambling key, but avoids spending
  // too long in the (slow) sweep across the entire memory.
  constraint num_trans_c { num_trans == 2; }
endclass
