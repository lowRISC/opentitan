// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (otp_ctrl_core_reg_block),
    .CFG_T               (otp_ctrl_env_cfg),
    .COV_T               (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (otp_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(otp_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_otp_ctrl_init = 1'b1;
  bit do_otp_pwr_init  = 1'b1;

  // To only write unused OTP address, sequence will collect all the written addresses to an
  // associative array to avoid `write_blank_addr_error`.
  bit write_unused_addr = 1;
  static bit used_dai_addrs[bit [OTP_ADDR_WIDTH - 1 : 0]];

  rand bit [NumOtpCtrlIntr-1:0] en_intr;
  bit is_valid_dai_op = 1;

  // According to spec, the period between digest calculation and reset should not issue any write.
  bit [NumPart-2:0] digest_calculated;

  // LC program request will use a separate variable to automatically set to non-blocking setting
  // when LC error bit is set.
  bit default_req_blocking = 1;
  bit lc_prog_blocking     = 1;

  uint32_t op_done_spinwait_timeout_ns = 20_000_000;

  // Collect current lc_state and lc_cnt. This is used to create next lc_state and lc_cnt without
  // error.
  lc_ctrl_state_pkg::lc_state_e lc_state;
  lc_ctrl_state_pkg::lc_cnt_e   lc_cnt;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // OTP has dut and edn reset. If assign OTP values after `super.dut_init()`, and if dut reset
    // deasserts earlier than edn reset, some OTP outputs might remain X or Z when dut clock is
    // running.
    otp_ctrl_vif_init();
    super.dut_init(reset_kind);

    cfg.backdoor_clear_mem = 0;
    // reset power init pin and lc pins
    if (do_otp_ctrl_init && do_apply_reset) otp_ctrl_init();
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    if (do_otp_pwr_init && do_apply_reset) otp_pwr_init();
  endtask

  // Cfg errors are cleared after reset
  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.ecc_err = OtpNoEccErr;
  endtask

  virtual task dut_shutdown();
    // check for pending otp_ctrl operations and wait for them to complete
    // TODO
  endtask

  virtual task otp_ctrl_vif_init();
    cfg.otp_ctrl_vif.drive_lc_creator_seed_sw_rw_en(On);
    cfg.otp_ctrl_vif.drive_lc_seed_hw_rd_en(randomize_lc_tx_t_val());
    cfg.otp_ctrl_vif.drive_lc_dft_en(Off);
    cfg.otp_ctrl_vif.drive_lc_escalate_en(Off);
    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);

    // Unused signals in open sourced OTP memory
    `DV_CHECK_RANDOMIZE_FATAL(cfg.dut_cfg)
    cfg.otp_ctrl_vif.otp_ast_pwr_seq_h_i    = cfg.dut_cfg.otp_ast_pwr_seq_h;
    cfg.otp_ctrl_vif.scan_en_i              = cfg.dut_cfg.scan_en;
    cfg.otp_ctrl_vif.scan_rst_ni            = cfg.dut_cfg.scan_rst_n;
    cfg.otp_ctrl_vif.scanmode_i             = cfg.dut_cfg.scanmode;
    cfg.otp_ctrl_vif.otp_vendor_test_ctrl_i = cfg.dut_cfg.otp_vendor_test_ctrl;
  endtask

  // drive otp_pwr req pin to initialize OTP, and wait until init is done
  virtual task otp_pwr_init();
    cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
    wait(cfg.otp_ctrl_vif.pwr_otp_done_o == 1);
    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);
    digest_calculated = 0;
  endtask

  // setup basic otp_ctrl features
  virtual task otp_ctrl_init();
    // reset memory to avoid readout X
    clear_otp_memory();
    lc_state = 0;
    lc_cnt   = 0;
  endtask

  virtual function void clear_otp_memory();
    cfg.mem_bkdr_util_h.clear_mem();
    cfg.backdoor_clear_mem = 1;
    used_dai_addrs.delete();
  endfunction

  // Overide this task for otp_ctrl_common_vseq and otp_ctrl_stress_all_with_rand_reset_vseq
  // because some registers won't set to default value until otp_init is done.
  virtual task read_and_check_all_csrs_after_reset();
    cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    otp_pwr_init();
    super.read_and_check_all_csrs_after_reset();
  endtask

  // this task triggers an OTP write sequence via the DAI interface
  virtual task dai_wr(bit [TL_DW-1:0] addr,
                      bit [TL_DW-1:0] wdata0,
                      bit [TL_DW-1:0] wdata1 = 0);
    bit [TL_DW-1:0] val;
    if (write_unused_addr) begin
      if (used_dai_addrs.exists(addr[OTP_ADDR_WIDTH - 1 : 0])) begin
        `uvm_info(`gfn, $sformatf("addr %0h is already written!", addr), UVM_MEDIUM)
        return;
      end else begin
        used_dai_addrs[addr] = 1;
      end
    end
    addr = randomize_dai_addr(addr);
    `uvm_info(`gfn, $sformatf("dai write addr %0h, data %0h", addr, wdata0), UVM_HIGH)
    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_wdata[0], wdata0);
    if (is_secret(addr) || is_sw_digest(addr)) csr_wr(ral.direct_access_wdata[1], wdata1);

    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiWrite));
    `uvm_info(`gfn, $sformatf("DAI write, address %0h, data0 %0h data1 %0h, is_secret = %0b",
              addr, wdata0, wdata1, is_secret(addr)), UVM_DEBUG)

    // Direct_access_regwen and dai_idle are checked only when following conditions are met:
    // - the dai operation is valid, otherwise it is hard to predict which cycle the error is
    //   detected
    // - zero delays in TLUL interface, otherwise dai operation might be finished before reading
    //   these two CSRs
    if (cfg.zero_delays && is_valid_dai_op &&
        cfg.otp_ctrl_vif.lc_escalate_en_i != lc_ctrl_pkg::On) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end
    wait_dai_op_done();
    rd_and_clear_intrs();
  endtask : dai_wr

  // This task triggers an OTP readout sequence via the DAI interface
  // If ecc_err is not OtpNoEccErr, will backdoor write to OTP and trigger an ECC error
  virtual task dai_rd(input  bit [TL_DW-1:0] addr,
                      input  otp_ecc_err_e   ecc_err,
                      output bit [TL_DW-1:0] rdata0,
                      output bit [TL_DW-1:0] rdata1);
    bit [TL_DW-1:0] val, backdoor_rd_val;
    bit backdoor_wr;
    addr = randomize_dai_addr(addr);

    // Here we won't backdoor write to corrupt ECC bits if:
    // 1. Current ECC error is uncorrectable already. Then the DAI access is locked and cannot read
    // any more.
    // 2. If dai read address is not valid (lc address or larger). Then DAI access will return
    // access error before reading the OTP bits.
    if (cfg.ecc_err != OtpEccUncorrErr && addr < LifeCycleOffset) begin
      if (ecc_err != OtpNoEccErr) begin
        backdoor_rd_val = backdoor_inject_ecc_err(addr, ecc_err);
        backdoor_wr = 1;
      end
      cfg.ecc_err = ecc_err;
    end

    csr_wr(ral.direct_access_address, addr);
    csr_wr(ral.direct_access_cmd, int'(otp_ctrl_pkg::DaiRead));

    if (cfg.zero_delays && is_valid_dai_op &&
        cfg.otp_ctrl_vif.lc_escalate_en_i != lc_ctrl_pkg::On) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end

    wait_dai_op_done();
    csr_rd(ral.direct_access_rdata[0], rdata0);
    if (is_secret(addr) || is_digest(addr)) csr_rd(ral.direct_access_rdata[1], rdata1);
    rd_and_clear_intrs();

    // If has ecc_err, backdoor write back original value
    // TODO: remove this once we can detect ECC error from men_bkdr_if
    if (backdoor_wr) begin
      cfg.mem_bkdr_util_h.write32({addr[TL_DW-3:2], 2'b00}, backdoor_rd_val);
    end
  endtask : dai_rd

  virtual task dai_rd_check(bit [TL_DW-1:0] addr,
                            bit [TL_DW-1:0] exp_data0,
                            bit [TL_DW-1:0] exp_data1 = 0);
    bit [TL_DW-1:0] rdata0, rdata1;
    dai_rd(addr, OtpNoEccErr, rdata0, rdata1);
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

    if (cfg.zero_delays && is_valid_dai_op &&
        cfg.otp_ctrl_vif.lc_escalate_en_i != lc_ctrl_pkg::On) begin
      csr_rd_check(ral.status.dai_idle, .compare_value(0), .backdoor(1));
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(val));
    end

    wait_dai_op_done();
    digest_calculated[part_idx] = 1;
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
  // Here to simplify testbench, write random data to sw digest.
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
    if (do_rd_lock[0]) csr_wr(ral.creator_sw_cfg_read_lock, 0);
    if (do_rd_lock[1]) csr_wr(ral.owner_sw_cfg_read_lock, 0);
  endtask

  // The digest CSR values are verified in otp_ctrl_scoreboard
  virtual task rd_digests();
    bit [TL_DW-1:0] val;
    csr_rd(.ptr(ral.creator_sw_cfg_digest[0]), .value(val));
    csr_rd(.ptr(ral.creator_sw_cfg_digest[1]), .value(val));
    csr_rd(.ptr(ral.owner_sw_cfg_digest[0]),   .value(val));
    csr_rd(.ptr(ral.owner_sw_cfg_digest[1]),   .value(val));
    csr_rd(.ptr(ral.hw_cfg_digest[0]),         .value(val));
    csr_rd(.ptr(ral.hw_cfg_digest[1]),         .value(val));
    csr_rd(.ptr(ral.secret0_digest[0]),        .value(val));
    csr_rd(.ptr(ral.secret0_digest[1]),        .value(val));
    csr_rd(.ptr(ral.secret1_digest[0]),        .value(val));
    csr_rd(.ptr(ral.secret1_digest[1]),        .value(val));
    csr_rd(.ptr(ral.secret2_digest[0]),        .value(val));
    csr_rd(.ptr(ral.secret2_digest[1]),        .value(val));
  endtask

  // This function backdoor inject error according to ecc_err.
  // For example, if err_mask is set to 'b01, bit 1 in OTP macro will be flipped.
  // This function will output original backdoor read data for the given address.
  virtual function bit [TL_DW-1:0] backdoor_inject_ecc_err(bit [TL_DW-1:0] addr,
                                                           otp_ecc_err_e   ecc_err);
    bit [TL_DW-1:0] val;
    addr = {addr[TL_DW-1:2], 2'b00};
    val = cfg.mem_bkdr_util_h.read32(addr);
    if (ecc_err == OtpNoEccErr || addr >= (LifeCycleOffset + LifeCycleSize)) return val;

    // Backdoor read and write back with error bits
    cfg.mem_bkdr_util_h.inject_errors(addr, (ecc_err == OtpEccUncorrErr) ? 2 : 1);
    `uvm_info(`gfn, $sformatf("original val %0h, addr %0h, err_type %0s",
                              val, addr, ecc_err.name), UVM_HIGH)
    return val;
  endfunction

  virtual task trigger_checks(bit [1:0]     val,
                              bit           wait_done = 1,
                              otp_ecc_err_e ecc_err = OtpNoEccErr);
    bit [TL_DW-1:0] backdoor_rd_val, addr;
    // Backdoor write ECC errors
    if (ecc_err != OtpNoEccErr) begin
      int part_idx = $urandom_range(HwCfgIdx, LifeCycleIdx);

      // Only HW cfgs check digest correctness
      if (part_idx != LifeCycleIdx) begin
        addr = $urandom_range(0, 1) ? PART_OTP_DIGEST_ADDRS[part_idx] << 2 :
                                      (PART_OTP_DIGEST_ADDRS[part_idx] + 1) << 2;
      end else begin
        addr = $urandom_range(LifeCycleOffset, LifeCycleOffset + LifeCycleSize - 1);
        addr = {addr[TL_DW-1:2], 2'b00};
      end
      backdoor_rd_val = backdoor_inject_ecc_err(addr, ecc_err);
      cfg.ecc_chk_err[part_idx] = ecc_err;
    end

    csr_wr(ral.check_trigger, val);
    if (wait_done && val) csr_spinwait(ral.status.check_pending, 0);

    if (ecc_err != OtpNoEccErr) begin
      cfg.mem_bkdr_util_h.write32(addr, backdoor_rd_val);
      cfg.ecc_chk_err = '{default: OtpNoEccErr};
    end
  endtask

  // For a DAI interface operation to finish, either way until status dai_idle is set, or check
  // err_code and see if fatal error happened.
  virtual task wait_dai_op_done();
    fork begin
      fork
        begin
          csr_spinwait(.ptr(ral.status.dai_idle),
                       .exp_data(1),
                       .timeout_ns(op_done_spinwait_timeout_ns),
                       .spinwait_delay_ns($urandom_range(0, 5)));
        end
        begin
          forever begin
            bit [TL_DW-1:0] err_val;
            cfg.clk_rst_vif.wait_clks(1);
            csr_rd(.ptr(ral.err_code[0].err_code[7]), .value(err_val), .backdoor(1));
            // Break if error will cause fatal alerts
            if (err_val inside {OTP_TERMINAL_ERRS}) break;
          end
        end
      join_any
      wait_no_outstanding_access();
      disable fork;
    end join
  endtask

  virtual task rd_and_clear_intrs();
    bit [TL_DW-1:0] val;
    if (cfg.otp_ctrl_vif.lc_prog_no_sta_check == 0) begin
      csr_rd(ral.intr_state, val);
      // In case lc_program request is issued after intr_state read
      if (cfg.otp_ctrl_vif.lc_prog_no_sta_check == 0) csr_wr(ral.intr_state, val);
    end
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

  // The following interface requests are separated to blocking and non-blocking accesses.
  // The non-blocking access is mainly used when lc_escalate_en is On, which acts like a reset and
  // move all design state machines to ErrorSt. Thus pending request will never get a response
  // until reset.
  virtual task req_sram_key(int index, bit blocking = default_req_blocking);
    // Return if the request is already high, this is mainly due to lc_escalate_en On.
    if (cfg.m_sram_pull_agent_cfg[index].vif.req === 1'b1) return;

    if (blocking) begin
      req_sram_key_sub(index);
    end else begin
      fork
        begin
          req_sram_key_sub(index);
        end
      join_none;
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task req_sram_key_sub(int index);
    push_pull_host_seq#(.DeviceDataWidth(SRAM_DATA_SIZE)) sram_pull_seq;
    wait(cfg.under_reset == 0);
    `uvm_create_on(sram_pull_seq, p_sequencer.sram_pull_sequencer_h[index]);
    `DV_CHECK_RANDOMIZE_FATAL(sram_pull_seq)
    `uvm_send(sram_pull_seq)
  endtask

  virtual task req_all_sram_keys(bit blocking = default_req_blocking);
    for (int i = 0; i < NumSramKeyReqSlots; i++) req_sram_key(i, blocking);
  endtask

  virtual task req_otbn_key(bit blocking = default_req_blocking);
    if (cfg.m_otbn_pull_agent_cfg.vif.req === 1'b1) return;

    if (blocking) begin
      req_otbn_key_sub();
    end else begin
      fork
        begin
          req_otbn_key_sub();
        end
      join_none;
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task req_otbn_key_sub();
    push_pull_host_seq#(.DeviceDataWidth(OTBN_DATA_SIZE)) otbn_pull_seq;
    wait(cfg.under_reset == 0);
    `uvm_create_on(otbn_pull_seq, p_sequencer.otbn_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(otbn_pull_seq)
    `uvm_send(otbn_pull_seq)
  endtask

  virtual task req_flash_addr_key(bit blocking = default_req_blocking);
    if (cfg.m_flash_addr_pull_agent_cfg.vif.req === 1'b1) return;

    if (blocking) begin
      req_flash_addr_key_sub();
    end else begin
      fork
        begin
          req_flash_addr_key_sub();
        end
      join_none;
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task req_flash_addr_key_sub();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_addr_pull_seq;
    wait(cfg.under_reset == 0);
    `uvm_create_on(flash_addr_pull_seq, p_sequencer.flash_addr_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_addr_pull_seq)
    `uvm_send(flash_addr_pull_seq)
  endtask

  virtual task req_flash_data_key(bit blocking = default_req_blocking);
    if (cfg.m_flash_data_pull_agent_cfg.vif.req === 1'b1) return;

    if (blocking) begin
      req_flash_data_key_sub();
    end else begin
      fork
        begin
          req_flash_data_key_sub();
        end
      join_none;
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task req_flash_data_key_sub();
    push_pull_host_seq#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_data_pull_seq;
    wait(cfg.under_reset == 0);
    `uvm_create_on(flash_data_pull_seq, p_sequencer.flash_data_pull_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(flash_data_pull_seq)
    `uvm_send(flash_data_pull_seq)
  endtask

  virtual task req_lc_transition(bit check_intr = 0,
                                 bit blocking = default_req_blocking,
                                 bit wr_blank_err = !write_unused_addr);
    if (cfg.m_lc_prog_pull_agent_cfg.vif.req === 1'b1) return;

    if (blocking) begin
      req_lc_transition_sub(check_intr, wr_blank_err);
    end else begin
      fork
        begin
          req_lc_transition_sub(check_intr, wr_blank_err);
        end
      join_none;
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task req_lc_transition_sub(bit check_intr = 0, bit wr_blank_err = !write_unused_addr);
    lc_ctrl_state_pkg::lc_cnt_e       next_lc_cnt;
    lc_ctrl_state_pkg::dec_lc_state_e next_lc_state, lc_state_dec;
    bit [TL_DW-1:0]                   intr_val;
    push_pull_host_seq#(.HostDataWidth(LC_PROG_DATA_SIZE), .DeviceDataWidth(1))
                        lc_prog_pull_seq;
    wait(cfg.under_reset == 0);
    `uvm_create_on(lc_prog_pull_seq, p_sequencer.lc_prog_pull_sequencer_h);

    if (!wr_blank_err) begin
      // Find valid next state and next cnt using lc_ctrl_dv_utils_pkg.
      // If terminal state or max LcCnt reaches, will not program any new data.
      if ((lc_state != LcStScrap) && (lc_cnt != LcCnt24)) begin
        lc_state_dec = lc_ctrl_dv_utils_pkg::dec_lc_state(lc_state);
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
                                           next_lc_state inside {VALID_NEXT_STATES[lc_state_dec]};)
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_cnt, next_lc_cnt > lc_cnt;)
        lc_state = lc_ctrl_dv_utils_pkg::encode_lc_state(next_lc_state);
        lc_cnt   = next_lc_cnt;
      end
      cfg.m_lc_prog_pull_agent_cfg.add_h_user_data({lc_cnt, lc_state});
    end

    `DV_CHECK_RANDOMIZE_FATAL(lc_prog_pull_seq)
    `uvm_send(lc_prog_pull_seq)

    if (check_intr) rd_and_clear_intrs();
  endtask

  // This test access OTP_CTRL's test_access memory. The open-sourced code only test if the access
  // is valid. Please override this task in proprietary OTP.
  virtual task otp_test_access();
    repeat($urandom_range(1, 20)) begin
      bit [TL_DW-1:0] addr = $urandom_range(TEST_ACCESS_BASE_ADDR,
                                            TEST_ACCESS_BASE_ADDR + TEST_ACCESS_WINDOW_SIZE - 1);
      bit [TL_DW-1:0] data = $urandom();
      bit [TL_DW-1:0] rdata;

      addr = cfg.ral.get_addr_from_offset(addr);
      `uvm_info(`gfn, $sformatf("write test access %0h with data %0h", addr, data), UVM_HIGH)
      tl_access(.addr(addr), .write(1), .data(data));
      tl_access(.addr(addr), .write(0), .data(rdata), .check_exp_data(1), .exp_data(data));
    end
  endtask

endclass : otp_ctrl_base_vseq
