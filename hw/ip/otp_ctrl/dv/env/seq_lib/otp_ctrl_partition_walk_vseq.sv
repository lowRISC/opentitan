// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence walk through all partitions via DAI access and TLUL interface
class otp_ctrl_partition_walk_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_partition_walk_vseq)

  `uvm_object_new

  virtual task body();
    for (int addr = CreatorSwCfgOffset / 4; addr < LifeCycleOffset / 4; addr++) begin
      int dai_addr = addr * 4;
      `uvm_info(`gfn, $sformatf("writing dai addr %0h", dai_addr), UVM_HIGH)

      // granularity of 64 bits
      if (is_secret(dai_addr) || is_digest(dai_addr)) begin
        if (dai_addr % 2 || !is_sw_digest(dai_addr)) continue;
        dai_wr(dai_addr, dai_addr, dai_addr + 1);
        dai_rd_check(dai_addr, dai_addr, dai_addr + 1);

      // granularity of 32 bits
      end else begin
        dai_wr(dai_addr, dai_addr);
        dai_rd_check(dai_addr, dai_addr);

        // check reading from tlul interface if it is sw partition
        if (is_sw_part(dai_addr)) begin
          bit [TL_DW-1:0] tlul_val;
          uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1));
          `DV_CHECK_EQ(tlul_val, dai_addr,
                       $sformatf("sw parts read out mismatch at tlul_addr %0h, dai_addr %0h",
                                  tlul_addr, dai_addr))
        end
      end
    end
  endtask

endclass
