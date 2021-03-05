// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests the bijectivity of the SRAM address remapping.
// To this, we iterate over every address in SRAM memory and write a unique value to it
// (in this case we write the address to memory, e.g. write 0x0 to address 0x0,
//  write 0x4 to address 0x4, etc...).
// We then read out each addres in memory and check that the read data is equal to the address
// we read it from (this is done using the built-in checking capabilities of `tl_acess()` task.
//
// This helps us verify that the SRAM address scrambling does not lead to any address collisions,
// e.g. addresses 0x4 and 0x8 do not both map to the same line in memory.
// If there are any address collisions, then we will read out an incorrect value from memory.
class sram_ctrl_bijection_vseq extends sram_ctrl_smoke_vseq;

  `uvm_object_utils(sram_ctrl_bijection_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[5 : 25]};
  }

  virtual task body();

    int sram_depth = cfg.mem_bkdr_vif.mem_depth;

    `uvm_info(`gfn, $sformatf("sram_depth: %0d", sram_depth), UVM_HIGH)

    for (int i = 0; i < num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("iteration: %0d", i), UVM_HIGH)

      // Write the corresponding address to each entry in the SRAM
      for (int j = 0; j < sram_depth; j++) begin
        do_single_write(.addr(j*4), .data(j*4), .mask('1));
      end

      // Read each location back, the read data should be the same as its address
      for (int j = 0; j < sram_depth; j++) begin
        logic [TL_DW-1:0] rdata;
        do_single_read(.addr(j*4), .mask('1), .check_rdata(1),
                       .exp_rdata(j*4), .rdata(rdata));
      end

      // request new scrambling key on all but the last iteration
      if (i != num_trans - 1) begin
        req_scr_key();
        csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1'b1));
      end

    end

  endtask : body

endclass
