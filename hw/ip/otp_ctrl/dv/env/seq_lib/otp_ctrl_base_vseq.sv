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
  bit [TL_AW-1:0] used_dai_addr_q[$];
  bit is_valid_dai_op = 1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.backdoor_clear_mem = 0;
    // reset power init pin and lc pins
    cfg.otp_ctrl_vif.init();
    if (do_otp_ctrl_init) otp_ctrl_init();
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    if (do_otp_pwr_init) otp_pwr_init();
  endtask

  // Cfg errors are cleared after reset
  virtual task apply_reset(string reset_kind = "HARD");
    super.apply_reset(reset_kind);
    cfg.ecc_err = OtpNoEccErr;
  endtask

  virtual task dut_shutdown();
    // check for pending otp_ctrl operations and wait for them to complete
    // TODO
  endtask

  // drive otp_pwr req pin to initialize OTP, and wait until init is done
  virtual task otp_pwr_init();
    cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
    wait(cfg.otp_ctrl_vif.pwr_otp_done_o == 1);
    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);
  endtask

  // setup basic otp_ctrl features
  virtual task otp_ctrl_init();
    // reset memory to avoid readout X
    cfg.mem_bkdr_vif.clear_mem();
    cfg.backdoor_clear_mem = 1;
    used_dai_addr_q.delete();
  endtask

  // some registers won't set to default value until otp_init is done
  virtual task read_and_check_all_csrs_after_reset();
    otp_pwr_init();
    super.read_and_check_all_csrs_after_reset();
  endtask

  // this task triggers an OTP write sequence via the DAI interface
  virtual task dai_wr(bit [TL_DW-1:0] addr,
                      bit [TL_DW-1:0] wdata0,
                      bit [TL_DW-1:0] wdata1 = 0);
    bit [TL_DW-1:0] val;
    addr = randomize_dai_addr(addr);
    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_wdata_0, wdata0);
    if (is_secret(addr) || is_sw_digest(addr)) csr_wr(ral.direct_access_wdata_1, wdata1);

    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiWrite));
    `uvm_info(`gfn, $sformatf("DAI write, address %0h, data0 %0h data1 %0h, is_secret = %0b",
              addr, wdata0, wdata1, is_secret(addr)), UVM_DEBUG)

    // Direct_access_regwen and dai_idle are checked only when following conditions are met:
    // - the dai operation is valid, otherwise it is hard to predict which cycle the error is
    //   detected
    // - zero delays in TLUL interface, otherwise dai operation might be finished before reading
    //   these two CSRs
    if (cfg.zero_delays && is_valid_dai_op) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end
    if (cfg.ecc_err == OtpEccUncorrErr) csr_spinwait(ral.status.dai_error, 1);
    else                                csr_spinwait(ral.status.dai_idle, 1);
    rd_and_clear_intrs();
  endtask : dai_wr

  // This task triggers an OTP readout sequence via the DAI interface
  // If ecc_err_mask is not 0, will backdoor write to OTP and trigger an ECC error
  virtual task dai_rd(input  bit [TL_DW-1:0] addr,
                      input  bit [TL_DW-1:0] ecc_err_mask,
                      output bit [TL_DW-1:0] rdata0,
                      output bit [TL_DW-1:0] rdata1);
    bit [TL_DW-1:0] val, backdoor_rd_val;
    bit backdoor_wr;
    addr = randomize_dai_addr(addr);
    if (cfg.ecc_err != OtpEccUncorrErr) begin
      backdoor_rd_val = backdoor_inject_ecc_err(addr, ecc_err_mask);
      backdoor_wr = 1;
    end

    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiRead));

    if (cfg.zero_delays && is_valid_dai_op) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end

    if (cfg.ecc_err == OtpEccUncorrErr) csr_spinwait(ral.status.dai_error, 1);
    else                                csr_spinwait(ral.status.dai_idle, 1);

    csr_rd(ral.direct_access_rdata_0, rdata0);
    if (is_secret(addr) || is_digest(addr)) csr_rd(ral.direct_access_rdata_1, rdata1);
    rd_and_clear_intrs();

    // If has ecc_err, backdoor write back original value
    // TODO: remove this once we can detect ECC error from men_bkdr_if
    if (cfg.ecc_err != OtpNoEccErr && backdoor_wr) begin
      cfg.mem_bkdr_vif.write32({addr[TL_DW-3:2], 2'b00}, backdoor_rd_val);
    end
  endtask : dai_rd

  virtual task dai_rd_check(bit [TL_DW-1:0] addr,
                            bit [TL_DW-1:0] exp_data0,
                            bit [TL_DW-1:0] exp_data1 = 0);
    bit [TL_DW-1:0] rdata0, rdata1;
    dai_rd(addr, 0, rdata0, rdata1);
    `DV_CHECK_EQ(rdata0, exp_data0, $sformatf("dai addr %0h rdata0 readout mismatch", addr))
    if (is_secret(addr) || is_digest(addr)) begin
      `DV_CHECK_EQ(rdata1, exp_data1, $sformatf("dai addr %0h rdata1 readout mismatch", addr))
    end
  endtask: dai_rd_check

  // this task exercises an OTP digest calculation via the DAI interface
  virtual task cal_digest(int part_idx);
    bit [TL_DW-1:0] val;
    csr_wr(ral.direct_access_address, PART_BASE_ADDRS[part_idx]);
    csr_wr(ral.direct_access_cmd, otp_ctrl_pkg::DaiDigest);

    if (cfg.zero_delays && is_valid_dai_op) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end

    if (cfg.ecc_err == OtpEccUncorrErr) csr_spinwait(ral.status.dai_error, 1);
    else                                csr_spinwait(ral.status.dai_idle, 1);
    rd_and_clear_intrs();
  endtask

  // this task provisions all HW partitions
  // SW partitions could not be provisioned via DAI interface
  // LC partitions cannot be locked
  virtual task cal_hw_digests(bit [3:0] trigger_digest = $urandom());
    for (int i = int'(HwCfgIdx); i < int'(LifeCycleIdx); i++) begin
      if (trigger_digest[i-HwCfgIdx]) cal_digest(i);
    end
  endtask

  // SW digest data are calculated in sw and won't be checked in OTP.
  // Here to simplify testbench, write random data to sw digest
  virtual task write_sw_digests(bit [1:0] wr_digest = $urandom());
    bit [TL_DW*2-1:0] wdata;
    if (wr_digest[0]) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata);
      dai_wr(CreatorSwCfgDigestOffset, wdata[TL_DW-1:0], wdata[TL_DW*2-1:TL_DW]);
    end
    if (wr_digest[1]) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata);
      dai_wr(OwnerSwCfgDigestOffset, wdata[TL_DW-1:0], wdata[TL_DW*2-1:TL_DW]);
    end
  endtask

  virtual task write_sw_rd_locks(bit [1:0] do_rd_lock= $urandom());
    if (do_rd_lock[0]) csr_wr(ral.creator_sw_cfg_read_lock, 1);
    if (do_rd_lock[1]) csr_wr(ral.owner_sw_cfg_read_lock, 1);
  endtask

  // The digest CSR values are verified in otp_ctrl_scoreboard
  virtual task rd_digests();
    bit [TL_DW-1:0] val;
    csr_rd(.ptr(ral.creator_sw_cfg_digest_0), .value(val));
    csr_rd(.ptr(ral.creator_sw_cfg_digest_1), .value(val));
    csr_rd(.ptr(ral.owner_sw_cfg_digest_0),   .value(val));
    csr_rd(.ptr(ral.owner_sw_cfg_digest_1),   .value(val));
    csr_rd(.ptr(ral.hw_cfg_digest_0),         .value(val));
    csr_rd(.ptr(ral.hw_cfg_digest_1),         .value(val));
    csr_rd(.ptr(ral.secret0_digest_0),        .value(val));
    csr_rd(.ptr(ral.secret0_digest_1),        .value(val));
    csr_rd(.ptr(ral.secret1_digest_0),        .value(val));
    csr_rd(.ptr(ral.secret1_digest_1),        .value(val));
    csr_rd(.ptr(ral.secret2_digest_0),        .value(val));
    csr_rd(.ptr(ral.secret2_digest_1),        .value(val));
  endtask

  // This function backdoor inject error according to err_mask.
  // For example, if err_mask is set to 'b01, bit 1 in OTP macro will be flipped.
  // This function will output original backdoor read data for the given address.
  // TODO: move it to mem_bkdr_if once #4794 landed
  virtual function bit [TL_DW-1:0] backdoor_inject_ecc_err(bit [TL_DW-1:0] addr,
                                                           bit [TL_DW-1:0] err_mask);
    bit [TL_DW-1:0] val, backdoor_val;
    addr = {addr[TL_DW-3:2], 2'b00};
    if (err_mask == 0 || addr >= LifeCycleOffset) begin
      cfg.ecc_err = OtpNoEccErr;
      return 0;
    end

    // If every byte at most has one ECC error bit, it is a correctable error
    // If any byte at more than one ECC error bit, it is a uncorrectable error
    cfg.ecc_err = OtpEccCorrErr;
    for (int i = 0; i < 2; i++) begin
      if (!$onehot(err_mask[i*16+:16]) && err_mask[i*16+:16]) begin
        cfg.ecc_err = OtpEccUncorrErr;
        break;
      end
    end

    // Backdoor read and write back with error bits
    val = cfg.mem_bkdr_vif.read32(addr);
    foreach (err_mask[i]) backdoor_val[i] = err_mask[i] ? ~val[i] : val[i];
    cfg.mem_bkdr_vif.write32(addr, backdoor_val);
    `uvm_info(`gfn, $sformatf("original val %0h, backdoor val %0h, err_mask %0h",
                              val, backdoor_val, err_mask), UVM_HIGH)

    return val;
  endfunction

  virtual task trigger_checks(bit [1:0] val, bit wait_done = 1);
    csr_wr(ral.check_trigger, val);
    if (wait_done && val) csr_spinwait(ral.status.check_pending, 0);
  endtask

  virtual task rd_and_clear_intrs();
    bit [TL_DW-1:0] val;
    if (cfg.otp_ctrl_vif.lc_prog_no_sta_check == 0) begin
      csr_rd(ral.intr_state, val);
      csr_wr(ral.intr_state, val);
    end
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

  virtual task req_flash_addr_key();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_addr_pull_seq;
    `uvm_create_on(flash_addr_pull_seq, p_sequencer.flash_addr_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_addr_pull_seq)
    `uvm_send(flash_addr_pull_seq)
  endtask

  virtual task req_flash_data_key();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_data_pull_seq;
    `uvm_create_on(flash_data_pull_seq, p_sequencer.flash_data_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_data_pull_seq)
    `uvm_send(flash_data_pull_seq)
  endtask

  virtual task req_lc_transition(bit check_intr = 0);
    lc_ctrl_state_pkg::lc_state_e lc_state;
    lc_ctrl_state_pkg::lc_cnt_e   lc_cnt;
    bit [TL_DW-1:0]               intr_val;
    push_pull_host_seq#(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1))
                        lc_prog_pull_seq;
    `uvm_create_on(lc_prog_pull_seq, p_sequencer.lc_prog_pull_sequencer_h);

    // Even though OTP does not check input lc_state or lc_cnt is valid enum,
    // this sequence will have 90% chance that the input data is correctly encoded
    if (!$urandom_range(0, 9)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(lc_state)
      `DV_CHECK_STD_RANDOMIZE_FATAL(lc_cnt)
      cfg.m_lc_prog_pull_agent_cfg.add_h_user_data({lc_state, lc_cnt});
    end

    `DV_CHECK_RANDOMIZE_FATAL(lc_prog_pull_seq)
    `uvm_send(lc_prog_pull_seq)

    if (check_intr) rd_and_clear_intrs();
  endtask

  virtual task req_lc_token();
    push_pull_host_seq#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) lc_token_pull_seq;
    `uvm_create_on(lc_token_pull_seq, p_sequencer.lc_token_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(lc_token_pull_seq)
    `uvm_send(lc_token_pull_seq)
  endtask

  // first two or three LSB bits of DAI address can be randomized based on if it is secret
  virtual function bit [TL_AW-1:0] randomize_dai_addr(bit [TL_AW-1:0] dai_addr);
    if (is_secret(dai_addr)) begin
      bit [2:0] rand_addr = $urandom();
      randomize_dai_addr = {dai_addr[TL_DW-1:3], rand_addr};
    end else begin
      bit [1:0] rand_addr = $urandom();
      randomize_dai_addr = {dai_addr[TL_DW-1:2], rand_addr};
    end
  endfunction

endclass : otp_ctrl_base_vseq
