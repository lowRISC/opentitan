// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_common_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_common_vseq)

  rand bit [TL_DW-1:0] dai_addr, wdata0, wdata1;

  constraint dai_addr_c {
    dai_addr dist {
        [0 : (PartInfo[LifeCycleIdx].offset - 1)]    :/ 1,
        [PartInfo[LifeCycleIdx].offset : {11{1'b1}}] :/ 1};
  }

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // drive dft_en pins to access the test_access memory
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
    // once turn on lc_dft_en regiser, will need some time to update the state register
    // two clock cycles for lc_async mode, one clock cycle for driving dft_en
    cfg.clk_rst_vif.wait_clks(3);
  endtask

  virtual task post_start();
    super.post_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit[TL_DW-1:0] exp_status_val, rdata0, rdata1;
    super.check_sec_cm_fi_resp(if_proxy);

    // Set expected status error val.
    for (int i = 0; i <= OtpLciErrIdx; i++) exp_status_val[i] = 1;
    if (!uvm_re_match("*.u_otp_ctrl_lfsr_timer*", if_proxy.path)) begin
      exp_status_val[OtpLfsrFsmErrIdx] = 1;
    end else if (!uvm_re_match("*u_otp_ctrl_kdi*", if_proxy.path)) begin
      exp_status_val[OtpDerivKeyFsmErrIdx] = 1;
    end else if (!uvm_re_match("*u_otp_ctrl_scrmbl*", if_proxy.path)) begin
      exp_status_val[OtpScramblingFsmErrIdx] = 1;
    end

    csr_rd_check(.ptr(ral.status), .compare_value(exp_status_val), .err_msg(
                 $sformatf("cm_fi status failed at injection %0s", if_proxy.sec_cm_type.name)));

    // Check OTP is locked after fault error.
    `DV_CHECK_RANDOMIZE_FATAL(this)
    is_valid_dai_op = 0;

    // Access OTP via DAI interface.
    dai_wr(dai_addr, wdata0, wdata1);
    dai_rd(dai_addr, rdata0, rdata1);
    `DV_CHECK_EQ(rdata0, 0)
    `DV_CHECK_EQ(rdata1, 0)
    if (is_sw_part(dai_addr)) begin
      uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
      tl_access(.addr(tlul_addr), .write(0), .data(rdata0), .blocking(1), .check_rsp(1),
                .exp_err_rsp(1), .exp_data('1));
    end
    cal_hw_digests();
    write_sw_digests();

    // Access OTP via app interface.
    if ($urandom_range(0, 1)) req_otbn_key(0);
    if ($urandom_range(0, 1)) req_flash_addr_key(0);
    if ($urandom_range(0, 1)) req_flash_data_key(0);
    if ($urandom_range(0, 1)) req_all_sram_keys(0);
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 20));

    csr_rd_check(.ptr(ral.status), .compare_value(exp_status_val),
                 .err_msg("status failure after OTP fatal fault error"));
  endtask : check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!enable) begin
          $assertoff(0, "tb.dut.gen_partitions[3].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[4].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[5].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[6].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[7].gen_lifecycle.u_part_buf.ScrmblDataKnown_A");
        end else begin
          $asserton(0, "tb.dut.gen_partitions[3].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[4].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[5].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[6].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[7].gen_lifecycle.u_part_buf.ScrmblDataKnown_A");
       end
      end
      SecCmPrimSparseFsmFlop: begin
        // No assertion error.
      end
      SecCmPrimDoubleLfsr: begin
        // No assertion error.
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase
  endfunction: sec_cm_fi_ctrl_svas

endclass
