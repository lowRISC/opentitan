// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
`define PART_ADDR_RANGE(i) \
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - DIGEST_SIZE - 1)]}

class otp_ctrl_sanity_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_sanity_vseq)

  `uvm_object_new

  randc bit [TL_AW-1:0]          dai_addr;
  rand  bit [TL_DW-1:0]          wdata0, wdata1;
  rand  int                      num_dai_wr;
  rand  otp_ctrl_part_pkg::part_idx_e part_idx;

  // TODO: temp -> no life-cycle partition involved
  constraint partition_index_c {
    part_idx inside {[CreatorSwCfgIdx:Secret2Idx]};
  }

  constraint dai_addr_c {
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

  constraint num_dai_wr_c {num_dai_wr inside {[1:20]};}

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // drive pwr_otp_req pin
    cfg.pwr_otp_vif.drive_pin(0, 1);
    wait(cfg.pwr_otp_vif.pins[2] == 1);
    cfg.lc_provision_en_vif.drive(lc_ctrl_pkg::On);
    csr_wr(ral.intr_enable, en_intr);
  endtask

  virtual task pre_start();
    super.pre_start();
    num_dai_wr.rand_mode(0);
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [TL_DW-1:0] rdata, tlul_rdata;
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d", i, num_trans), UVM_MEDIUM)
      do_otp_ctrl_init = 1;
      dut_init();
      do_otp_ctrl_init = 0;

      // after otp-init done, check status
      cfg.clk_rst_vif.wait_clks(1);
      csr_rd_check(.ptr(ral.status), .compare_value(OtpIdle));

      // get sram keys
      req_all_sram_keys();

      // get otbn keys
      req_otbn_key();

      // get flash addr and data
      req_flash_addr();
      req_flash_data();

      for (int i = 0; i < num_dai_wr; i++) begin
        bit [TL_DW-1:0] rdata0, rdata1;
        `DV_CHECK_RANDOMIZE_FATAL(this)

        // OTP write via DAI
        dai_wr(dai_addr, wdata0, wdata1);

        // OTP read via DAI
        dai_rd(dai_addr, rdata0, rdata1);

        // check read data
        `DV_CHECK_EQ(wdata0, rdata0, $sformatf("read data0 mismatch at addr %0h", dai_addr))
        if (!is_secret(dai_addr)) begin
          `DV_CHECK_EQ(wdata1, rdata1, $sformatf("read data1 mismatch at addr %0h", dai_addr))
        end

        // if write sw partitions, check tlul window
        if (part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx}) begin
          bit [TL_AW-1:0] tlul_addr = get_sw_window_addr(dai_addr);

          // random issue reset, OTP content should not be cleared
          if ($urandom_range(0, 1)) dut_init();
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_rdata), .blocking(1));
          `DV_CHECK_EQ(tlul_rdata, rdata0, $sformatf("mem read out mismatch at addr %0h", tlul_addr))
        end
      end

      // check no error
      csr_rd_check(.ptr(ral.status), .compare_value(OtpIdle));

      // lock HW digests
      `uvm_info(`gfn, "Trigger HW digest calculation", UVM_HIGH)
      cal_hw_digests();
      csr_rd_check(.ptr(ral.status), .compare_value(OtpIdle));
    end
  endtask : body

endclass : otp_ctrl_sanity_vseq

`undef PART_ADDR_RANGE
