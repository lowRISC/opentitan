// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence force host read to non data partition
// to trigger fatal error.
class flash_ctrl_phy_host_grant_err_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_host_grant_err_vseq)
  `uvm_object_new

  task run_error_event();
    int delay;
    bit add_err;
    string path = "tb.dut.u_eflash.gen_flash_cores[0].u_core.muxed_part";

    cfg.scb_h.exp_alert["fatal_err"] = 1;
    cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    repeat (2) begin
      // unit 100 ns;
      delay = $urandom_range(1, 10);
      #(delay * 100ns);

      if (add_err) begin
        `DV_CHECK(uvm_hdl_release(path))
      end else begin
        // This can haapen when host_read is sent to info partition (by force).
        // After that, fatal error happen. So turning off these assertion
        // just to make sure test run to complete.
        $assertoff(0, "tb.dut.u_sw_rd_fifo.DataKnown_A");
        $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rd_storage.DataKnown_A");
        $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rd_storage.DataKnown_A");
        $assertoff(0, "tb.dut.tlul_assert_device.gen_device.dDataKnown_A");
        $assertoff(0, "tb.dut.RspPayLoad_A");
        $assertoff(0, "tb.dut.u_reg_core.u_socket.gen_dfifo[0].fifo_d.rspfifo.DataKnown_A");
        $assertoff(0, "tb.dut.u_reg_core.u_socket.gen_dfifo[1].fifo_d.rspfifo.DataKnown_A");
        $assertoff(0, "tb.dut.u_reg_core.u_socket.fifo_h.rspfifo.DataKnown_A");
        $assertoff(0, "tb.dut.u_to_rd_fifo.TlOutPayloadKnown_A");
        $assertoff(0, "tb.dut.u_to_rd_fifo.u_rspfifo.DataKnown_A");
        $assertoff(0, "tb.dut.tlul_assert_device.dKnown_A");

        // set error counter high number to skip unpredictable error
        cfg.scb_h.exp_tl_rsp_intg_err = 1;
        cfg.tlul_eflash_exp_cnt = 1;
        cfg.tlul_core_exp_cnt = 1;
        cfg.otf_scb_h.comp_off = 1;

        add_err = 1;
        @(posedge cfg.flash_ctrl_vif.host_gnt);
        `DV_CHECK(uvm_hdl_force(path, 1))

      end
    end // repeat (2)

    check_fault(ral.fault_status.host_gnt_err);
    cfg.tlul_core_exp_cnt = cfg.tlul_core_obs_cnt;
  endtask

  task launch_host_rd();
    bit [TL_AW-1:0] tl_addr;
    bit             saw_err, completed;
    data_4s_t rdata;

    for (int i = 0; i < cfg.otf_num_hr; ++i) begin
      tl_addr[OTFHostId-2:0] = $urandom();
      tl_addr[OTFBankId] = $urandom_range(0, 1);
      fork
        tl_access_w_abort(
                          .addr(tl_addr), .write(1'b0), .completed(completed),
                          .saw_err(saw_err),
                          .tl_access_timeout_ns(cfg.seq_cfg.erase_timeout_ns),
                          .data(rdata), .check_rsp(1'b0), .blocking(1),
                          .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.flash_ral_name]));

      join_none
      #0;
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask // launch_host_rd
endclass
