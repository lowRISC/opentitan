// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq to walk through DAI states and request keys
`define PART_ADDR_RANGE(i) \
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - DIGEST_SIZE - 1)]}

class otp_ctrl_smoke_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_smoke_vseq)

  `uvm_object_new

  bit do_lc_trans;
  bit collect_used_addr = 1;

  rand bit                           access_locked_parts;
  rand bit [TL_AW-1:0]               dai_addr;
  rand bit [TL_DW-1:0]               wdata0, wdata1;
  rand int                           num_dai_op;
  rand otp_ctrl_part_pkg::part_idx_e part_idx;

  constraint no_access_err_c {access_locked_parts == 0;}

  // LC partition does not allow DAI access
  constraint partition_index_c {
    part_idx inside {[CreatorSwCfgIdx:Secret2Idx]};
  }

  constraint dai_wr_legal_addr_c {
    if (part_idx == CreatorSwCfgIdx) dai_addr inside `PART_ADDR_RANGE(CreatorSwCfgIdx);
    if (part_idx == OwnerSwCfgIdx)   dai_addr inside `PART_ADDR_RANGE(OwnerSwCfgIdx);
    if (part_idx == HwCfgIdx)        dai_addr inside `PART_ADDR_RANGE(HwCfgIdx);
    if (part_idx == Secret0Idx)      dai_addr inside `PART_ADDR_RANGE(Secret0Idx);
    if (part_idx == Secret1Idx)      dai_addr inside `PART_ADDR_RANGE(Secret1Idx);
    if (part_idx == Secret2Idx)      dai_addr inside `PART_ADDR_RANGE(Secret2Idx);
    if (part_idx == LifeCycleIdx)    dai_addr inside `PART_ADDR_RANGE(LifeCycleIdx);
  }

  constraint dai_wr_blank_addr_c {
    dai_addr inside {used_dai_addr_q} == 0;
    dai_addr % 4 == 0;
    if (part_idx inside {[Secret0Idx:Secret2Idx]}) dai_addr % 8 == 0;
  }

  constraint num_iterations_c {
    num_trans  inside {[1:20]};
    num_dai_op inside {[1:50]};
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    csr_wr(ral.intr_enable, en_intr);
  endtask

  virtual task pre_start();
    super.pre_start();
    num_dai_op.rand_mode(0);
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [TL_DW-1:0] tlul_val;
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d", i, num_trans), UVM_LOW)

      // to avoid access locked OTP partions, issue reset and clear the OTP memory to all 0.
      if (access_locked_parts == 0) begin
        do_otp_ctrl_init = 1;
        if (i > 1) dut_init();
        // after otp-init done, check status
        cfg.clk_rst_vif.wait_clks(1);
        csr_rd_check(.ptr(ral.status), .compare_value(OtpDaiIdle));
      end
      do_otp_ctrl_init = 0;

      for (int i = 0; i < num_dai_op; i++) begin
        bit [TL_DW-1:0] rdata0, rdata1;

        `DV_CHECK_RANDOMIZE_FATAL(this)
        // recalculate part_idx in case some test turn off constraint dai_wr_legal_addr_c
        part_idx = get_part_index(dai_addr);
        `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d with addr %0h in partition %0d",
                  i, num_dai_op, dai_addr, part_idx), UVM_DEBUG)

        // OTP write via DAI
        if ($urandom_range(0, 1)) begin
          dai_wr(dai_addr, wdata0, wdata1);
          if (collect_used_addr) used_dai_addr_q.push_back(dai_addr);
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
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1));
        end

        if ($urandom_range(0, 1)) csr_rd(.ptr(ral.status), .value(tlul_val));
      end

      // lock digests
      `uvm_info(`gfn, "Trigger HW digest calculation", UVM_HIGH)
      cal_hw_digests();
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.status), .value(tlul_val));
      write_sw_digests();
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.status), .value(tlul_val));
      write_sw_rd_locks();

      if ($urandom_range(0, 1)) rd_digests();
      dut_init();

      // read and check digest in scb
      rd_digests();

      if (do_lc_trans) begin
        req_lc_transition();
        req_lc_token();
      end
    end

  endtask : body

endclass : otp_ctrl_smoke_vseq

`undef PART_ADDR_RANGE
