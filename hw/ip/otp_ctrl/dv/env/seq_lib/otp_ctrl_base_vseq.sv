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
  bit do_otp_pwr_init  = 1'b1;

  rand bit [NumOtpCtrlIntr-1:0] en_intr;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.backdoor_clear_mem = 0;
    // reset power init pin and lc pins
    cfg.pwr_otp_vif.drive_pin(OtpPwrInitReq, 0);
    cfg.lc_provision_en_vif.drive(lc_ctrl_pkg::Off);
    cfg.lc_dft_en_vif.drive(lc_ctrl_pkg::Off);
    if (do_otp_ctrl_init) otp_ctrl_init();
    if (do_otp_pwr_init) otp_pwr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending otp_ctrl operations and wait for them to complete
    // TODO
  endtask

  // drive otp_pwr req pin to initialize OTP, and wait until init is done
  virtual task otp_pwr_init();
    cfg.pwr_otp_vif.drive_pin(OtpPwrInitReq, 1);
    wait(cfg.pwr_otp_vif.pins[OtpPwrDoneRsp] == 1);
    cfg.pwr_otp_vif.drive_pin(OtpPwrInitReq, 0);
  endtask

  // setup basic otp_ctrl features
  virtual task otp_ctrl_init();
    // reset memory to avoid readout X
    cfg.mem_bkdr_vif.clear_mem();
    cfg.backdoor_clear_mem = 1;
  endtask

  // some registers won't set to default value until otp_init is done
  virtual task read_and_check_all_csrs_after_reset();
    // drive dft_en pins to access the test_access memory
    cfg.lc_dft_en_vif.drive(lc_ctrl_pkg::On);
    otp_pwr_init();
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
    csr_wr(ral.direct_access_address, PART_BASE_ADDRS[part_idx]);
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

  // TODO: support checking all partitions within OTP
  // The digest CSR values are verified in otp_ctrl_scoreboard
  virtual task check_digests();
    bit [TL_DW-1:0] val;
    csr_rd(.ptr(ral.hw_cfg_digest_0),  .value(val));
    csr_rd(.ptr(ral.hw_cfg_digest_1),  .value(val));
    csr_rd(.ptr(ral.secret0_digest_0), .value(val));
    csr_rd(.ptr(ral.secret0_digest_1), .value(val));
    csr_rd(.ptr(ral.secret1_digest_0), .value(val));
    csr_rd(.ptr(ral.secret1_digest_1), .value(val));
    csr_rd(.ptr(ral.secret2_digest_0), .value(val));
    csr_rd(.ptr(ral.secret2_digest_1), .value(val));
  endtask

  virtual task req_sram_key(int index);
    push_pull_host_seq#(.DeviceDataWidth(SRAM_DATA_SIZE)) sram_pull_seq;
    `uvm_create_on(sram_pull_seq, p_sequencer.sram_pull_sequencer_h[index]);
    `DV_CHECK_RANDOMIZE_FATAL(sram_pull_seq)
    `uvm_send(sram_pull_seq)
  endtask

  virtual task req_all_sram_keys();
    for (int i = 0; i < NumSramKeyReqSlots; i++) req_sram_key(i);
  endtask

  virtual task req_otbn_key();
    push_pull_host_seq#(.DeviceDataWidth(OTBN_DATA_SIZE)) otbn_pull_seq;
    `uvm_create_on(otbn_pull_seq, p_sequencer.otbn_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(otbn_pull_seq)
    `uvm_send(otbn_pull_seq)
  endtask

  virtual task req_flash_addr();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_addr_pull_seq;
    `uvm_create_on(flash_addr_pull_seq, p_sequencer.flash_addr_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_addr_pull_seq)
    `uvm_send(flash_addr_pull_seq)
  endtask

  virtual task req_flash_data();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_data_pull_seq;
    `uvm_create_on(flash_data_pull_seq, p_sequencer.flash_data_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_data_pull_seq)
    `uvm_send(flash_data_pull_seq)
  endtask

endclass : otp_ctrl_base_vseq
