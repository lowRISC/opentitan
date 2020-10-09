// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (otp_ctrl_reg_block),
    .CFG_T               (otp_ctrl_env_cfg),
    .COV_T               (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (otp_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(otp_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_otp_ctrl_init = 1'b1;

  rand bit [NumOtpCtrlIntr-1:0] en_intr;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.pwr_otp_vif.drive_pin(0, 0);
    cfg.lc_provision_en_vif.drive(lc_ctrl_pkg::Off);
    // reset power init pin and lc_provision_en pin
    if (do_otp_ctrl_init) otp_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending otp_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic otp_ctrl features
  virtual task otp_ctrl_init();
    // reset memory to avoid readout X
    cfg.mem_bkdr_vif.clear_mem();
    csr_wr(ral.intr_enable, en_intr);
  endtask

  // this task triggers an OTP write sequence via the DAI interface
  virtual task dai_wr(bit [TL_DW-1:0] addr,
                      bit [TL_DW-1:0] wdata0,
                      bit [TL_DW-1:0] wdata1 = 0);
    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_wdata_0, wdata0);
    if (!is_secret(addr)) csr_wr(ral.direct_access_wdata_1, wdata1);
    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiWrite));
    csr_spinwait(ral.intr_state, 1 << OtpOperationDone);
    csr_wr(ral.intr_state, 1'b1 << OtpOperationDone);
  endtask : dai_wr

  // this task triggers an OTP readout sequence via the DAI interface
  virtual task dai_rd(bit [TL_DW-1:0]        addr,
                      output bit [TL_DW-1:0] rdata0,
                      output bit [TL_DW-1:0] rdata1);
    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiRead));
    csr_spinwait(ral.intr_state, 1 << OtpOperationDone);

    csr_rd(ral.direct_access_rdata_0, rdata0);
    if (!is_secret(addr)) csr_rd(ral.direct_access_rdata_1, rdata1);
    csr_wr(ral.intr_state, 1'b1 << OtpOperationDone);
  endtask : dai_rd

  // this task exercises an OTP digest calculation via the DAI interface
  virtual task cal_digest(int part_idx);
    csr_wr(ral.direct_access_address, DIGESTS_ADDR[part_idx]);
    csr_wr(ral.direct_access_cmd, otp_ctrl_pkg::DaiDigest);
    csr_spinwait(ral.intr_state, 1 << OtpOperationDone);
    csr_wr(ral.intr_state, 1 << OtpOperationDone);
  endtask

  // this task provisions all HW partitions
  // SW partitions could not be provisioned via DAI interface
  // LC partitions cannot be locked
  virtual task cal_hw_digests();
    for (int i = int'(HwCfgIdx); i < int'(LifeCycleIdx); i++) begin
      cal_digest(i);
    end
  endtask

endclass : otp_ctrl_base_vseq
