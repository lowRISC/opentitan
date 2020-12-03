// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq to walk through DAI states and request keys
`define PART_ADDR_RANGE(i) \
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - DIGEST_SIZE - 1)]}

class otp_ctrl_smoke_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_smoke_vseq)

  `uvm_object_new

  rand bit [TL_AW-1:0]               dai_addr;
  rand bit [TL_DW-1:0]               wdata0, wdata1;
  rand int                           num_dai_op;
  rand otp_ctrl_part_pkg::part_idx_e part_idx;

  // LC partition does not allow DAI access
  constraint partition_index_c {
    part_idx inside {[CreatorSwCfgIdx:Secret2Idx]};
    part_idx != HwCfgIdx;
  }

  constraint dai_addr_c {
    dai_addr inside {used_dai_addr_q} == 0;
    if (part_idx == CreatorSwCfgIdx) dai_addr inside `PART_ADDR_RANGE(CreatorSwCfgIdx);
    if (part_idx == OwnerSwCfgIdx)   dai_addr inside `PART_ADDR_RANGE(OwnerSwCfgIdx);
    if (part_idx == HwCfgIdx)        dai_addr inside `PART_ADDR_RANGE(HwCfgIdx);
    if (part_idx == Secret0Idx)      dai_addr inside `PART_ADDR_RANGE(Secret0Idx);
    if (part_idx == Secret1Idx)      dai_addr inside `PART_ADDR_RANGE(Secret1Idx);
    if (part_idx == Secret2Idx)      dai_addr inside `PART_ADDR_RANGE(Secret2Idx);
    if (part_idx == LifeCycleIdx)    dai_addr inside `PART_ADDR_RANGE(LifeCycleIdx);

    dai_addr % 4 == 0;
    if (part_idx inside {[Secret0Idx:Secret2Idx]}) dai_addr % 8 == 0;
  }

  constraint num_dai_op_c {num_dai_op inside {[1:50]};}

  constraint num_trans_c {num_trans inside {[1:20]};}

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.lc_provision_wr_en_vif.drive(lc_ctrl_pkg::On);
    csr_wr(ral.intr_enable, en_intr);
  endtask

  virtual task pre_start();
    super.pre_start();
    num_dai_op.rand_mode(0);
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d", i, num_trans), UVM_MEDIUM)
      do_otp_ctrl_init = 1;
      if (i > 1) dut_init();
      do_otp_ctrl_init = 0;

      // after otp-init done, check status
      cfg.clk_rst_vif.wait_clks(1);
      csr_rd_check(.ptr(ral.status), .compare_value(OtpDaiIdle));

      // get sram keys
      req_all_sram_keys();

      // get otbn keys
      req_otbn_key();

      // get flash addr and data
      req_flash_addr();
      req_flash_data();

      for (int i = 0; i < num_dai_op; i++) begin
        bit [TL_DW-1:0] rdata0, rdata1, tlul_rdata;
        `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d", i, num_dai_op), UVM_DEBUG)
        `DV_CHECK_RANDOMIZE_FATAL(this)

        // OTP write via DAI
        if ($urandom_range(0, 1)) begin
          dai_wr(dai_addr, wdata0, wdata1);
          used_dai_addr_q.push_back(dai_addr);
        end

        if ($urandom_range(0, 1)) begin
          // OTP read via DAI, check data in scb
          dai_rd(dai_addr, rdata0, rdata1);
        end

        // if write sw partitions, check tlul window
        if (part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx} && ($urandom_range(0, 1))) begin
          uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));

          // random issue reset, OTP content should not be cleared
          if ($urandom_range(0, 1)) dut_init();
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_rdata), .blocking(1));
        end
      end

      // check no error
      csr_rd_check(.ptr(ral.status), .compare_value(OtpDaiIdle));

      // lock HW digests
      `uvm_info(`gfn, "Trigger HW digest calculation", UVM_HIGH)
      cal_hw_digests();
      write_sw_digests();
      csr_rd_check(.ptr(ral.status), .compare_value(OtpDaiIdle));
      dut_init();

      // check digest
      check_digests();
    end

  endtask : body

endclass : otp_ctrl_smoke_vseq

`undef PART_ADDR_RANGE
