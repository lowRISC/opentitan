// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(otp_ctrl_env_cfg),
    .RAL_T(otp_ctrl_reg_block),
    .COV_T(otp_ctrl_env_cov)
  );
  `uvm_component_utils(otp_ctrl_scoreboard)

  // local variables
  bit [TL_DW-1:0] otp_a [OTP_ARRAY_SIZE];

  // lc_state and lc_cnt that stored in OTP
  bit [LC_PROG_DATA_SIZE-1:0] otp_lc_data;
  bit [EDN_BUS_WIDTH-1:0]     edn_data_q[$];

  // This flag is used when reset is issued during otp dai write access.
  bit dai_wr_ip;
  int dai_digest_ip = LifeCycleIdx; // Default to LC as it does not have digest.
  bit ignore_digest_chk = 0;

  // This bit is used for DAI interface to mark if the read access is valid.
  bit dai_read_valid;

  // Status related variables
  bit under_chk, under_dai_access;
  bit [TL_DW-1:0] exp_status, status_mask;

  otp_alert_e exp_alert = OtpNoAlert;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(SRAM_DATA_SIZE)))
                        sram_fifos[NumSramKeyReqSlots];
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(OTBN_DATA_SIZE)))  otbn_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_addr_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_data_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE)))
                        lc_prog_fifo;

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      sram_fifos[i] = new($sformatf("sram_fifos[%0d]", i), this);
    end
    otbn_fifo       = new("otbn_fifo", this);
    flash_addr_fifo = new("flash_addr_fifo", this);
    flash_data_fifo = new("flash_data_fifo", this);
    lc_prog_fifo    = new("lc_prog_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_otp_power_up();
      process_lc_esc();
      process_lc_prog_req();
      process_edn_req();
      check_otbn_rsp();
      check_flash_rsps();
      check_sram_rsps();
      recover_lc_prog_req();
    join_none
  endtask

  // This task process the following logic in during otp_power_up:
  // 1. After reset deasserted, otp access is locked until pwr_otp_done_o is set
  // 2. After reset deasserted, if power otp_init request is on, and if testbench uses backdoor to
  //    clear OTP memory to all zeros, clear all digests and re-calculate secret partitions
  virtual task process_otp_power_up();
    if (cfg.en_scb) begin
      forever begin
        @(posedge cfg.otp_ctrl_vif.pwr_otp_init_i) begin
          if (cfg.backdoor_clear_mem) begin
            bit [SCRAMBLE_DATA_SIZE-1:0] data = descramble_data(0, Secret0Idx);
            otp_a        = '{default:0};
            otp_lc_data  = '{default:0};
            // secret partitions have been scrambled before writing to OTP.
            // here calculate the pre-srambled raw data when clearing internal OTP to all 0s.
            for (int i = SECRET0_START_ADDR; i <= SECRET0_END_ADDR; i++) begin
              otp_a[i] = ((i - SECRET0_START_ADDR) % 2) ? data[SCRAMBLE_DATA_SIZE-1:TL_DW] :
                                                          data[TL_DW-1:0];
            end
            data = descramble_data(0, Secret1Idx);
            for (int i = SECRET1_START_ADDR; i <= SECRET1_END_ADDR; i++) begin
              otp_a[i] = ((i - SECRET1_START_ADDR) % 2) ? data[SCRAMBLE_DATA_SIZE-1:TL_DW] :
                                                          data[TL_DW-1:0];
            end
            data = descramble_data(0, Secret2Idx);
            for (int i = SECRET2_START_ADDR; i <= SECRET2_END_ADDR; i++) begin
              otp_a[i] = ((i - SECRET2_START_ADDR) % 2) ? data[SCRAMBLE_DATA_SIZE-1:TL_DW] :
                                                          data[TL_DW-1:0];
            end
            predict_digest_csrs();
            `uvm_info(`gfn, "clear internal memory and digest", UVM_HIGH)
          end
        end
        @(posedge cfg.otp_ctrl_vif.pwr_otp_done_o || cfg.under_reset ||
                  cfg.otp_ctrl_vif.alert_reqs) begin
          if (!cfg.under_reset && !cfg.otp_ctrl_vif.alert_reqs) begin
            otp_ctrl_part_pkg::otp_hw_cfg_data_t exp_hwcfg_data;
            otp_ctrl_pkg::otp_keymgr_key_t       exp_keymgr_data;
            bit [otp_ctrl_pkg::KeyMgrKeyWidth-1:0] exp_keymgr_key0, exp_keymgr_key1;

            if (dai_digest_ip != LifeCycleIdx) begin
              bit [TL_DW-1:0] otp_addr = PART_OTP_DIGEST_ADDRS[dai_digest_ip];
              otp_a[otp_addr]   = cfg.mem_bkdr_vif.read32(otp_addr << 2);
              otp_a[otp_addr+1] = cfg.mem_bkdr_vif.read32((otp_addr << 2) + 4);
              dai_digest_ip = LifeCycleIdx;
            end
            predict_digest_csrs();

            if (cfg.otp_ctrl_vif.under_error_states() == 0) begin
              // Dai access is unlocked because the power init is done
              void'(ral.direct_access_regwen.predict(1));

              // Dai idle is set because the otp init is done
              exp_status[OtpDaiIdleIdx] = 1;
            end

            // Hwcfg_o gets data from OTP HW cfg partition
            exp_hwcfg_data = cfg.otp_ctrl_vif.under_error_states() ?
                             otp_ctrl_part_pkg::PartInvDefault[HwCfgOffset*8 +: HwCfgSize*8] :
                             otp_hw_cfg_data_t'({<<32 {otp_a[HwCfgOffset/4 +: HwCfgSize/4]}});
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.otp_hw_cfg_o.data, exp_hwcfg_data)

            if (!cfg.otp_ctrl_vif.under_error_states()) begin
              `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.count, otp_lc_data[0 +: LcCountWidth])
              `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.state,
                           otp_lc_data[LcCountWidth +: LcStateWidth])
            end

            // Otp_keymgr outputs creator root key shares from the secret2 partition.
            // Depends on lc_seed_hw_rd_en_i, it will output the real keys or a constant
            exp_keymgr_data.valid = get_otp_digest_val(Secret2Idx) != 0;
            if (cfg.otp_ctrl_vif.lc_seed_hw_rd_en_i == lc_ctrl_pkg::On) begin
              exp_keymgr_data.key_share0 =
                  {<<32 {otp_a[CreatorRootKeyShare0Offset/4 +: CreatorRootKeyShare0Size/4]}};
              exp_keymgr_data.key_share1 =
                  {<<32 {otp_a[CreatorRootKeyShare1Offset/4 +: CreatorRootKeyShare1Size/4]}};
            end else begin
              exp_keymgr_data.key_share0 =
                  PartInvDefault[CreatorRootKeyShare0Offset*8 +: CreatorRootKeyShare0Size*8];
              exp_keymgr_data.key_share1 =
                  PartInvDefault[CreatorRootKeyShare1Offset*8 +: CreatorRootKeyShare1Size*8];
            end
            // Check keymgr_key_o in otp_ctrl_if
            if (cfg.otp_ctrl_vif.under_error_states() == 0) begin
              `DV_CHECK_EQ(cfg.otp_ctrl_vif.keymgr_key_o, exp_keymgr_data)
            end
          end else if (cfg.otp_ctrl_vif.alert_reqs) begin
            // Ignore digest CSR check when otp_ctrl initialization is interrupted by fatal errors.
            // SCB cannot predict how many partitions already finished initialization and updated
            // the digest value to CSRs.
            ignore_digest_chk = 1;
          end
          if (cfg.en_cov) begin
            bit [NumPart-2:0] parts_locked;
            foreach (parts_locked[i]) parts_locked[i] = (get_otp_digest_val(i) != 0);
            cov.power_on_cg.sample(cfg.otp_ctrl_vif.lc_esc_on, parts_locked);
          end
        end
      end
    end
  endtask

  // This task monitors internal escalation triggered by two methods:
  // 1. Externally lc_escalation_en is set to lc_ctrl_pkg::On.
  // 2. Internal fatal alert triggered and all partitions are driven to error states.
  virtual task process_lc_esc();
    forever begin
      wait(cfg.otp_ctrl_vif.alert_reqs == 1 && cfg.en_scb);
      if (cfg.otp_ctrl_vif.lc_esc_on == 0) `DV_CHECK_NE(exp_alert, OtpNoAlert)

      if (exp_alert != OtpCheckAlert) set_exp_alert("fatal_check_error", 1, 5);

      // If the lc_escalation is triggered by internal fatal alert, wait 2 negedge until status is
      // updated internally
      if (cfg.otp_ctrl_vif.lc_esc_on == 0) begin
        cfg.clk_rst_vif.wait_n_clks(2);
        exp_status[OtpCheckPendingIdx] = 0;
        exp_status[OtpDaiIdleIdx] = 0;
      end else begin
        exp_status = '0;
        // Only lc_esc_on will set these bits to 1.
        exp_status[OtpDerivKeyFsmErrIdx:OtpLfsrFsmErrIdx] = '1;
      end

      // Update status bits.
      for (int i = 0; i < OtpTimeoutErrIdx; i++) begin
        predict_err(.status_err_idx(otp_status_e'(i)), .err_code(OtpFsmStateError),
                    .update_esc_err(1));
      end

      // Update digest values and direct_access_regwen.
      predict_rdata(1, 0, 0);
      void'(ral.direct_access_regwen.predict(.value(0), .kind(UVM_PREDICT_READ)));

      // DAI access is locked until reset, so no need to backdoor read otp write value until reset.

      wait(cfg.otp_ctrl_vif.alert_reqs == 0);
    end
  endtask

  // This task monitors if lc_program req is interrupted by reset.
  // If it happens, scb cannot predict how many bits have been written to OTP_CTRL.
  // So here we will backdoor read back OTP lc partitions bits.
  virtual task recover_lc_prog_req();
    forever begin
      wait (cfg.otp_ctrl_vif.lc_prog_req == 1);
      wait (cfg.otp_ctrl_vif.lc_prog_req == 0);
      // Wait one 1ps to avoid race condition.
      #1ps;
      if (cfg.otp_ctrl_vif.rst_ni == 0) begin
        for (int i = 0; i < LC_PROG_DATA_SIZE/32; i++) begin
          otp_lc_data[i*32+:32] = cfg.mem_bkdr_vif.read32(LifeCycleOffset+i*4);
        end
      end
    end
  endtask

  virtual task process_lc_prog_req();
    forever begin
      push_pull_item#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE)) rcv_item;
      bit        exp_err_bit;
      bit [15:0] rcv_words [LC_PROG_DATA_SIZE/16];

      lc_prog_fifo.get(rcv_item);

      // LCI is updated by OTP word.
      rcv_words = {<< 16{rcv_item.h_data}};
      foreach (rcv_words[i]) begin
        bit [15:0] curr_word = otp_lc_data[i*16 +: 16];
        if ((curr_word & rcv_words[i]) == curr_word) otp_lc_data[i*16 +: 16] = rcv_words[i];
        else                                         exp_err_bit = 1;
      end

      if (exp_err_bit) predict_err(OtpLciErrIdx, OtpMacroWriteBlankError);
      else             predict_no_err(OtpLciErrIdx);

      // LC program request data is valid means no OTP macro error.
      `DV_CHECK_EQ(rcv_item.d_data, exp_err_bit)

      if (cfg.en_cov) cov.lc_prog_cg.sample(exp_err_bit);
    end
  endtask

  virtual task process_edn_req();
    forever begin
      push_pull_item#(.DeviceDataWidth(EDN_DATA_WIDTH)) edn_item;
      edn_fifo.get(edn_item);
      edn_data_q.push_back(edn_item.d_data[EDN_BUS_WIDTH-1:0]);
    end
  endtask

  virtual task check_otbn_rsp();
    forever begin
      push_pull_item#(.DeviceDataWidth(OTBN_DATA_SIZE)) rcv_item;
      bit [SCRAMBLE_KEY_SIZE-1:0]  edn_key2, edn_key1;
      bit [SCRAMBLE_KEY_SIZE-1:0]  sram_key;
      bit [SCRAMBLE_DATA_SIZE-1:0] exp_key_lower, exp_key_higher;
      bit [OtbnKeyWidth-1:0]       key, exp_key;
      bit [OtbnNonceWidth-1:0]     nonce, exp_nonce;
      bit                          seed_valid;
      bit                          part_locked;

      otbn_fifo.get(rcv_item);
      seed_valid  = rcv_item.d_data[0];
      nonce       = rcv_item.d_data[1+:OtbnNonceWidth];
      key         = rcv_item.d_data[OtbnNonceWidth+1+:OtbnKeyWidth];
      part_locked = {`gmv(ral.secret1_digest_0), `gmv(ral.secret1_digest_1)} != '0;

      // seed is valid as long as secret1 is locked
      `DV_CHECK_EQ(seed_valid, part_locked, "otbn seed_valid mismatch")

      // If edn_data_q matches the OTBN requested size, check OTBN outputs
      if (edn_data_q.size() == NUM_OTBN_EDN_REQ) begin
        {exp_nonce, edn_key2, edn_key1} = {<<32{edn_data_q}};

        // check nonce value
        `DV_CHECK_EQ(nonce, exp_nonce, "otbn nonce mismatch")

        // calculate key
        sram_key = get_key_from_otp(part_locked, SramDataKeySeedOffset / 4);
        exp_key_lower = present_encode_with_final_const(
                        .data(RndCnstDigestIV[SramDataKey]),
                        .key(sram_key),
                        .final_const(RndCnstDigestConst[SramDataKey]),
                        .second_key(edn_key1),
                        .num_round(2));

        exp_key_higher = present_encode_with_final_const(
                         .data(RndCnstDigestIV[SramDataKey]),
                         .key(sram_key),
                         .final_const(RndCnstDigestConst[SramDataKey]),
                         .second_key(edn_key2),
                         .num_round(2));
        exp_key = {exp_key_higher, exp_key_lower};
        `DV_CHECK_EQ(key, exp_key, "otbn key mismatch")

        if (cfg.en_cov) cov.otbn_req_cg.sample(part_locked);

      // If during OTBN key request, the LFSR timer expired and trigger an EDN request to acquire
      // two EDN keys, then ignore the OTBN output checking, because scb did not know which EDN
      // keys are used for LFSR.
      // Thus any edn_data_q size equal to (16+2*N) is exempted from checking.
      end else if ((edn_data_q.size() - NUM_OTBN_EDN_REQ) % 2 != 0) begin
        `uvm_error(`gfn, $sformatf("Unexpected edn_data_q size (%0d) during OTBN request",
                                   edn_data_q.size()))
      end
      edn_data_q.delete();
    end
  endtask

  virtual task check_flash_rsps();
    for (int i = FlashDataKey; i <= FlashAddrKey; i++) begin
      automatic digest_sel_e sel_flash = i;
      fork
        forever begin
          push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE)) rcv_item;
          bit [SCRAMBLE_KEY_SIZE-1:0]  flash_key;
          bit [SCRAMBLE_DATA_SIZE-1:0] exp_key_lower, exp_key_higher;
          bit [FlashKeyWidth-1:0]      key, exp_key;
          bit                          seed_valid, part_locked;
          int                          flash_key_index;

          if (sel_flash == FlashAddrKey) begin
            flash_addr_fifo.get(rcv_item);
            flash_key_index = FlashAddrKeySeedOffset / 4;
          end else begin
            flash_data_fifo.get(rcv_item);
            flash_key_index = FlashDataKeySeedOffset / 4;
          end
          seed_valid  = rcv_item.d_data[0];
          key         = rcv_item.d_data[1+:FlashKeyWidth];
          part_locked = {`gmv(ral.secret1_digest_0), `gmv(ral.secret1_digest_1)} != '0;
          `DV_CHECK_EQ(seed_valid, part_locked,
                      $sformatf("flash %0s seed_valid mismatch", sel_flash.name()))

          // calculate key
          flash_key = get_key_from_otp(part_locked, flash_key_index);
          exp_key_lower = present_encode_with_final_const(
                          .data(RndCnstDigestIV[sel_flash]),
                          .key(flash_key),
                          .final_const(RndCnstDigestConst[sel_flash]));

          flash_key = get_key_from_otp(part_locked, flash_key_index + 4);
          exp_key_higher = present_encode_with_final_const(
                           .data(RndCnstDigestIV[sel_flash]),
                           .key(flash_key),
                           .final_const(RndCnstDigestConst[sel_flash]));
          exp_key = {exp_key_higher, exp_key_lower};
          `DV_CHECK_EQ(key, exp_key, $sformatf("flash %s key mismatch", sel_flash.name()))

          if (cfg.en_cov) cov.flash_req_cg.sample(sel_flash, part_locked);
        end
      join_none;
    end
  endtask

  virtual task check_sram_rsps();
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      automatic int index = i;
      fork
        forever begin
          push_pull_item#(.DeviceDataWidth(SRAM_DATA_SIZE)) rcv_item;
          sram_key_t                   key, exp_key;
          sram_nonce_t                 nonce, exp_nonce;
          bit                          seed_valid, part_locked;
          bit [SCRAMBLE_KEY_SIZE-1:0]  edn_key2, edn_key1;
          bit [SCRAMBLE_KEY_SIZE-1:0]  sram_key; // key used as input to present algo
          bit [SCRAMBLE_DATA_SIZE-1:0] exp_key_lower, exp_key_higher;

          sram_fifos[index].get(rcv_item);
          seed_valid = rcv_item.d_data[0];
          part_locked = {`gmv(ral.secret1_digest_0), `gmv(ral.secret1_digest_1)} != '0;

          // seed is valid as long as secret1 is locked
          `DV_CHECK_EQ(seed_valid, part_locked, $sformatf("sram_%0d seed_valid mismatch", index))

          // If edn_data_q matches the OTBN requested size, check OTBN outputs
          if (edn_data_q.size() == NUM_SRAM_EDN_REQ) begin
            {exp_nonce, edn_key2, edn_key1} = {<<32{edn_data_q}};

            // check nonce value
            `DV_CHECK_EQ(nonce, exp_nonce, $sformatf("sram_%0d nonce mismatch", index))

            // calculate key
            sram_key = get_key_from_otp(part_locked, SramDataKeySeedOffset / 4);
            exp_key_lower = present_encode_with_final_const(
                            .data(RndCnstDigestIV[SramDataKey]),
                            .key(sram_key),
                            .final_const(RndCnstDigestConst[SramDataKey]),
                            .second_key(edn_key1),
                            .num_round(2));

            exp_key_higher = present_encode_with_final_const(
                             .data(RndCnstDigestIV[SramDataKey]),
                             .key(sram_key),
                             .final_const(RndCnstDigestConst[SramDataKey]),
                             .second_key(edn_key2),
                             .num_round(2));
            exp_key = {exp_key_higher, exp_key_lower};
            `DV_CHECK_EQ(key, exp_key, $sformatf("sram_%0d key mismatch", index))
            if (cfg.en_cov) cov.sram_req_cg.sample(index, part_locked);

          end else if ((edn_data_q.size() - NUM_SRAM_EDN_REQ) % 2 != 0) begin
            `uvm_error(`gfn, $sformatf("Unexpected edn_data_q size (%0d) during SRAM request",
                                       edn_data_q.size()))
          end
          edn_data_q.delete();
        end
      join_none
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg     csr;
    dv_base_reg dv_reg;
    bit         do_read_check = 1;
    bit         write         = item.is_write();
    uvm_reg_addr_t csr_addr   = ral.get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] addr_mask = ral.get_addr_mask();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_reg, csr)
    // SW CFG window
    end else if ((csr_addr & addr_mask) inside
        {[SW_WINDOW_BASE_ADDR : SW_WINDOW_BASE_ADDR + SW_WINDOW_SIZE]}) begin
      if (data_phase_read) begin
        bit [TL_AW-1:0] otp_addr = (csr_addr & addr_mask - SW_WINDOW_BASE_ADDR) >> 2;
        // TODO: macro ecc uncorrectable error once mem_bkdr_if supports
        //`DV_CHECK_EQ(item.d_data, 0,
        //             $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
        //             csr_addr, otp_addr << 2))
        `DV_CHECK_EQ(item.d_data, otp_a[otp_addr],
                     $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
                     csr_addr, otp_addr << 2))
      end
      return;
    // TEST ACCESS window
    end else if ((csr_addr & addr_mask) inside
         {[TEST_ACCESS_BASE_ADDR : TEST_ACCESS_BASE_ADDR + TEST_ACCESS_WINDOW_SIZE]}) begin
      return;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (addr_phase_write) begin
      // Skip predict if the register is locked by `direct_access_regwen`.
      if (ral.direct_access_regwen.locks_reg_or_fld(dv_reg) &&
          `gmv(ral.direct_access_regwen) == 0) return;

      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        if (data_phase_read) begin
          // Disable intr_state checking when lc_program is in progress, because scb cannot
          // accurately predict when program_error will be triggered.
          // We will check the intr_state after lc_program request is done, and the error bit will
          // be checked in the `process_lc_prog_req` task.
          if (cfg.otp_ctrl_vif.lc_prog_no_sta_check) do_read_check = 0;
            if (do_read_check) begin
              bit [TL_DW-1:0] intr_en           = `gmv(ral.intr_enable);
              bit [NumOtpCtrlIntr-1:0] intr_exp = `gmv(ral.intr_state);

              foreach (intr_exp[i]) begin
              otp_intr_e intr = otp_intr_e'(i);
              `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
                                $sformatf("Interrupt_pin: %0s", intr.name));
              if (cfg.en_cov) begin
                cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
                cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
              end
            end
          end
        end
      end
      "intr_test": begin
        if (addr_phase_write) begin
          bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
          bit [NumOtpCtrlIntr-1:0] intr_exp = `gmv(ral.intr_state) | item.a_data;

          void'(ral.intr_state.predict(.value(intr_exp)));
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
      end
      "direct_access_cmd": begin
        if (addr_phase_write && !cfg.otp_ctrl_vif.under_error_states()) begin
          // here only normalize to 2 lsb, if is secret, will be reduced further
          bit [TL_AW-1:0] dai_addr = `gmv(ral.direct_access_address) >> 2 << 2;
          int part_idx = get_part_index(dai_addr);
          void'(ral.direct_access_regwen.predict(0));
          under_dai_access = 1;

          // LC partition cannot be access via DAI
          if (part_idx == LifeCycleIdx) begin
            predict_err(OtpDaiErrIdx, OtpAccessError);
            if (item.a_data == DaiRead) predict_rdata(is_secret(dai_addr), 0, 0);
          end else begin
            case (item.a_data)
              DaiDigest: cal_digest_val(part_idx);
              DaiRead: begin
                // Check if it is sw partition read lock
                bit sw_read_lock = 0;
                if (part_idx == CreatorSwCfgIdx) begin
                  sw_read_lock = `gmv(ral.creator_sw_cfg_read_lock) == 0;
                end else if (part_idx == OwnerSwCfgIdx) begin
                  sw_read_lock = `gmv(ral.owner_sw_cfg_read_lock) == 0;
                end

                    // SW partitions write read_lock_csr can lock read access.
                if (sw_read_lock ||
                    // Secret partitions cal digest can also lock read access.
                    // However, digest is always readable except SW partitions (Issue #5752).
                    (is_secret(dai_addr) && get_digest_reg_val(part_idx) != 0 &&
                     !is_digest(dai_addr)) ||
                    // If the partition is secret2 and lc_creator_seed_sw_rw is disable, then
                    // return access error.
                    (part_idx == Secret2Idx && !is_digest(dai_addr) &&
                     cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i == lc_ctrl_pkg::Off)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                  predict_rdata(is_secret(dai_addr) || is_digest(dai_addr), 0, 0);
                  // DAI interface access error, even though injected ECC error, it won't be read
                  // out and detected. (TODO: can remove this once ECC is adopted in mem_bkdr_if)
                  cfg.ecc_err = OtpNoEccErr;

                end else begin
                  bit [TL_AW-1:0] otp_addr = get_scb_otp_addr();
                  if (cfg.ecc_err == OtpNoEccErr) begin
                    predict_no_err(OtpDaiErrIdx);
                    predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                  otp_a[otp_addr], otp_a[otp_addr+1]);
                  end else if (cfg.ecc_err == OtpEccCorrErr) begin
                    predict_err(OtpDaiErrIdx, OtpMacroEccCorrError);
                    predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                  otp_a[otp_addr], otp_a[otp_addr+1]);
                    // In sequence, we backdoor write back to non-error value, so here scb reset
                    // the ecc_err back to NoErr.
                    cfg.ecc_err = OtpNoEccErr;

                  // OTP macro uncorrectable error: DAI interface goes to error state
                  end else begin
                    predict_err(OtpDaiErrIdx, OtpMacroEccUncorrError);
                    // Max wait 20 clock cycles because scb did not know when exactly OTP will
                    // finish reading and reporting the uncorrectable error.
                    set_exp_alert("fatal_macro_error", 1, 20);
                    predict_rdata(1, 0, 0);
                  end
                end
              end
              DaiWrite: begin
                bit[TL_AW-1:0] otp_addr = get_scb_otp_addr();
                // check if write locked
                if (get_digest_reg_val(part_idx) != 0 ||
                    (part_idx == Secret2Idx && !is_digest(dai_addr) &&
                     cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i == lc_ctrl_pkg::Off)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                end else begin
                  predict_no_err(OtpDaiErrIdx);
                  // write digest
                  if (is_sw_digest(dai_addr)) begin
                    bit [TL_DW*2-1:0] curr_digest, prev_digest;
                    curr_digest = {`gmv(ral.direct_access_wdata_1),
                                   `gmv(ral.direct_access_wdata_0)};
                    prev_digest = {otp_a[otp_addr+1], otp_a[otp_addr]};
                    // allow bit write
                    if ((prev_digest & curr_digest) == prev_digest) begin
                      update_digest_to_otp(part_idx, curr_digest);
                      dai_wr_ip = 1;
                    end else begin
                      predict_err(OtpDaiErrIdx, OtpMacroWriteBlankError);
                    end
                  end else if (is_digest(dai_addr)) begin
                    predict_err(OtpDaiErrIdx, OtpAccessError);
                  // write OTP memory
                  end else begin
                    dai_wr_ip = 1;
                    if (!is_secret(dai_addr)) begin
                      bit [TL_DW-1:0] wr_data = `gmv(ral.direct_access_wdata_0);
                      // allow bit write
                      if ((otp_a[otp_addr] & wr_data) == otp_a[otp_addr]) begin
                        otp_a[otp_addr] = wr_data;
                        check_otp_idle(.val(0), .wait_clks(3));
                      end else begin
                        predict_err(OtpDaiErrIdx, OtpMacroWriteBlankError);
                      end
                    end else begin
                      bit [SCRAMBLE_DATA_SIZE-1:0] secret_data = {otp_a[otp_addr + 1],
                                                                  otp_a[otp_addr]};
                      bit [SCRAMBLE_DATA_SIZE-1:0] wr_data = {`gmv(ral.direct_access_wdata_1),
                                                              `gmv(ral.direct_access_wdata_0)};
                      wr_data = scramble_data(wr_data, part_idx);
                      secret_data = scramble_data(secret_data, part_idx);
                      if ((secret_data & wr_data) == secret_data) begin
                        otp_a[otp_addr]     = `gmv(ral.direct_access_wdata_0);
                        otp_a[otp_addr + 1] = `gmv(ral.direct_access_wdata_1);
                        // wait until secret scrambling is done
                        check_otp_idle(.val(0), .wait_clks(34));
                      end else begin
                        predict_err(OtpDaiErrIdx, OtpMacroWriteBlankError);
                      end
                    end
                  end
                end
              end
              default: begin
                `uvm_fatal(`gfn, $sformatf("invalid cmd: %0d", item.a_data))
              end
            endcase
            // regwen is set to 0 only if the dai operation is successfully
            if (`gmv(ral.intr_state.otp_error) == 0) void'(ral.direct_access_regwen.predict(0));
          end
        end
      end
      "status": begin
        if (addr_phase_read) begin
          void'(ral.status.predict(.value(exp_status), .kind(UVM_PREDICT_READ)));

          // update status mask
          status_mask = 0;
          // Mask out check_pending field - we do not know how long it takes to process checks.
          // Check failure can trigger all kinds of errors.
          if (under_chk) status_mask = '1;

          // Mask out otp_dai access related field - we do not know how long it takes to finish
          // DAI access.
          if (under_dai_access) begin
            status_mask[OtpDaiIdleIdx] = 1;
            status_mask[OtpDaiErrIdx]  = 1;
          end

          // Mask out LCI error bit if lc_req is set.
          if (cfg.otp_ctrl_vif.lc_prog_no_sta_check) status_mask[OtpLciErrIdx] = 1;

        end else if (data_phase_read) begin
          if (item.d_data[OtpDaiIdleIdx]) begin
            check_otp_idle(1);
            dai_wr_ip = 0;
            dai_digest_ip = LifeCycleIdx;
          end

          // STATUS register check with mask
          if (do_read_check) begin
            `DV_CHECK_EQ((csr.get_mirrored_value() | status_mask), (item.d_data | status_mask),
                         $sformatf("reg name: status, compare_mask %0h", status_mask))
          end

          // Check if OtpCheckPending is set correctly, then ignore checking until check is done
          if (under_chk) begin
            if (item.d_data[OtpCheckPendingIdx] == 0) begin
              exp_status[OtpCheckPendingIdx] = 0;
              under_chk = 0;
            end
          end

          if (under_dai_access && !cfg.otp_ctrl_vif.under_error_states()) begin
            if (item.d_data[OtpDaiIdleIdx]) begin
              under_dai_access = 0;
              void'(ral.direct_access_regwen.predict(1));
              void'(ral.intr_state.otp_operation_done.predict(1));
            end
          end
        end
        // checked in this block above
        do_read_check = 0;
      end
      "check_trigger": begin
        if (addr_phase_write && `gmv(ral.check_trigger_regwen) && item.a_data inside {[1:3]}) begin
          exp_status[OtpCheckPendingIdx] = 1;
          under_chk = 1;
          if (`gmv(ral.check_timeout) > 0 && `gmv(ral.check_timeout) <= CHK_TIMEOUT_CYC) begin
            set_exp_alert("fatal_check_error", 1, `gmv(ral.check_timeout));
            predict_err(OtpTimeoutErrIdx);
          end else begin
            if (get_field_val(ral.check_trigger.consistency, item.a_data)) begin
              foreach(cfg.ecc_chk_err[i]) begin
                if (cfg.ecc_chk_err[i] == OtpEccCorrErr) predict_err(i, OtpMacroEccCorrError);
              end
            end
          end
        end
      end
      "err_code": begin
        // If lc_prog in progress, err_code might update anytime in DUT. Ignore checking until req
        // is acknowledged.
        if (cfg.m_lc_prog_pull_agent_cfg.vif.req) do_read_check = 0;
      end
      "hw_cfg_digest_0", "hw_cfg_digest_1", "secret0_digest_0", "secret0_digest_1",
      "secret1_digest_0", "secret1_digest_1", "secret2_digest_0", "secret2_digest_1",
      "creator_sw_cfg_digest_0", "creator_sw_cfg_digest_1", "owner_sw_cfg_digest_0",
      "owner_sw_cfg_digest_1": begin
        if (ignore_digest_chk) do_read_check = 0;
      end
      "direct_access_regwen", "direct_access_wdata_0", "direct_access_wdata_1",
      "direct_access_address", "direct_access_rdata_0", "direct_access_rdata_1",
      "check_regwen", "check_trigger_regwen", "check_trigger", "check_timeout", "intr_enable",
      "creator_sw_cfg_read_lock", "owner_sw_cfg_read_lock", "integrity_check_period",
      "consistency_check_period", "alert_test": begin
        // Do nothing
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // If reset or lc_escalate_en is issued during otp program, this function will backdoor update
  // otp memory write value because scb did not know how many cells haven been written.
  // We won't update csr `direct_access_address` after fatal alert happened, so in this function
  // we can directly call method `get_scb_otp_addr` to get the interrupted dai address.
  virtual function void recover_interrupted_op();
    if (dai_wr_ip) begin
      bit [TL_DW-1:0] otp_addr = get_scb_otp_addr();
      bit [TL_DW-1:0] dai_addr = otp_addr << 2;
      otp_a[otp_addr] = cfg.mem_bkdr_vif.read32(dai_addr);

      if (is_secret(dai_addr)) begin
        int part_idx = get_part_index(dai_addr);
        bit [TL_DW*2-1:0] mem_rd_val      = cfg.mem_bkdr_vif.read64(dai_addr);
        bit [TL_DW*2-1:0] descrabmled_val = descramble_data(mem_rd_val, part_idx);
        otp_a[otp_addr+1] = descrabmled_val[TL_DW*2-1:TL_DW];
        otp_a[otp_addr]   = descrabmled_val[TL_DW-1:0];
      end
      dai_wr_ip = 0;
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    recover_interrupted_op();
    super.reset(kind);
    // flush fifos
    otbn_fifo.flush();
    flash_addr_fifo.flush();
    flash_data_fifo.flush();
    lc_prog_fifo.flush();
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      sram_fifos[i].flush();
    end

    under_chk             = 0;
    under_dai_access      = 0;
    ignore_digest_chk     = 0;
    exp_status            = `gmv(ral.status);
    exp_alert             = OtpNoAlert;

    edn_data_q.delete();

    // Out of reset: lock dai access until power init is done
    if (cfg.en_scb) void'(ral.direct_access_regwen.predict(0));
  endfunction

  virtual function void check_otp_idle(bit val, int wait_clks = 0);
    fork
      begin
        fork
          begin
            // use negedge to avoid race condition
            cfg.clk_rst_vif.wait_n_clks(wait_clks + 1);
            `uvm_error(`gfn,
                       $sformatf("pwr_otp_idle output is %0b while expect %0b within %0d cycles",
                       cfg.otp_ctrl_vif.pwr_otp_idle_o, val, wait_clks))
          end
          begin
            wait(cfg.under_reset || cfg.otp_ctrl_vif.pwr_otp_idle_o == val ||
                 // Due to OTP access arbitration, any KDI request during DAI access might block
                 // write secret until KDI request is completed. Since the KDI process time could
                 // vary depends on the push-pull-agent, we are going to ignore the checking if
                 // this scenario happens.
                 cfg.m_otbn_pull_agent_cfg.vif.req ||
                 cfg.m_flash_data_pull_agent_cfg.vif.req ||
                 cfg.m_flash_addr_pull_agent_cfg.vif.req ||
                 cfg.m_sram_pull_agent_cfg[0].vif.req ||
                 cfg.m_sram_pull_agent_cfg[1].vif.req ||
                 cfg.m_lc_prog_pull_agent_cfg.vif.req ||
                 // When lc_escalation is on, the DAI interface goes to ErrorSt, so ignore
                 // otp_idle checking.
                 cfg.otp_ctrl_vif.alert_reqs ||
                 // Check timeout will keep doing background check, issue #5616
                 exp_status[OtpTimeoutErrIdx]);
          end
        join_any
        disable fork;
      end
    join_none
  endfunction

  // predict digest registers
  virtual function void predict_digest_csrs();
    void'(ral.creator_sw_cfg_digest_0.predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[CreatorSwCfgIdx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.creator_sw_cfg_digest_1.predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[CreatorSwCfgIdx] + 1]), .kind(UVM_PREDICT_DIRECT)));

    void'(ral.owner_sw_cfg_digest_0.predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[OwnerSwCfgIdx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.owner_sw_cfg_digest_1.predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[OwnerSwCfgIdx] + 1]), .kind(UVM_PREDICT_DIRECT)));

    void'(ral.hw_cfg_digest_0.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[HwCfgIdx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.hw_cfg_digest_1.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[HwCfgIdx] + 1]), .kind(UVM_PREDICT_DIRECT)));

    void'(ral.secret0_digest_0.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret0Idx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret0_digest_1.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret0Idx] + 1]), .kind(UVM_PREDICT_DIRECT)));

    void'(ral.secret1_digest_0.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret1Idx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret1_digest_1.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret1Idx] + 1]), .kind(UVM_PREDICT_DIRECT)));

    void'(ral.secret2_digest_0.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret2Idx]]), .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret2_digest_1.predict(.value(cfg.otp_ctrl_vif.under_error_states() ? 0 :
          otp_a[PART_OTP_DIGEST_ADDRS[Secret2Idx] + 1]), .kind(UVM_PREDICT_DIRECT)));
  endfunction

  function void update_digest_to_otp(int part_idx, bit [TL_DW*2-1:0] digest);
    otp_a[PART_OTP_DIGEST_ADDRS[part_idx]]     = digest[31:0];
    otp_a[PART_OTP_DIGEST_ADDRS[part_idx] + 1] = digest[63:32];
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

  // Calculate digest value for each partition
  // According to the design spec, the calculation is based on 64-rounds of PRESENT cipher
  // The 64-bit data_in state is initialized with a silicon creator constant, and each 128 bit
  // chunk of partition data are fed in as keys
  // The last 64-round PRESENT calculation will use a global digest constant as key input
  function void cal_digest_val(int part_idx);
    bit [NUM_ROUND-1:0] [SCRAMBLE_DATA_SIZE-1:0] enc_array;
    bit [SCRAMBLE_DATA_SIZE-1:0]                 init_vec = RndCnstDigestIV[0];
    bit [TL_DW-1:0]   mem_q[$];
    int               array_size;
    real              key_factor  = SCRAMBLE_KEY_SIZE / TL_DW;
    bit [TL_DW*2-1:0] digest, prev_digest;

    if (cfg.otp_ctrl_vif.under_error_states()) return;

    if (get_digest_reg_val(part_idx) != 0 ||
        part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx, LifeCycleIdx}) begin
      predict_err(OtpDaiErrIdx, OtpAccessError);
      return;
    end else if (part_idx == Secret2Idx &&
                 cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i == lc_ctrl_pkg::Off) begin
      predict_err(OtpDaiErrIdx, OtpAccessError);
      return;
    end else begin
      predict_no_err(OtpDaiErrIdx);
      dai_digest_ip = part_idx;
    end
    case (part_idx)
      HwCfgIdx:   mem_q = otp_a[HW_CFG_START_ADDR:HW_CFG_END_ADDR];
      Secret0Idx: mem_q = otp_a[SECRET0_START_ADDR:SECRET0_END_ADDR];
      Secret1Idx: mem_q = otp_a[SECRET1_START_ADDR:SECRET1_END_ADDR];
      Secret2Idx: mem_q = otp_a[SECRET2_START_ADDR:SECRET2_END_ADDR];
      default: begin
        `uvm_fatal(`gfn, $sformatf("Access unexpected partition %0d", part_idx))
      end
    endcase

    array_size = mem_q.size();

    // for secret partitions, need to use otp scrambled value as data input
    if (part_idx inside {[Secret0Idx:Secret2Idx]}) begin
      bit [TL_DW-1:0] scrambled_mem_q[$];
      for (int i = 0; i < array_size/2; i++) begin
        bit [SCRAMBLE_DATA_SIZE-1:0] scrambled_data;
        scrambled_data = scramble_data({mem_q[i*2+1], mem_q[i*2]}, part_idx);
        scrambled_mem_q.push_back(scrambled_data[TL_DW-1:0]);
        scrambled_mem_q.push_back(scrambled_data[SCRAMBLE_DATA_SIZE-1:TL_DW]);
      end
      mem_q = scrambled_mem_q;
    end

    for (int i = 0; i < $ceil(array_size / key_factor); i++) begin
      bit [SCRAMBLE_DATA_SIZE-1:0] input_data = (i == 0) ? init_vec : digest;
      bit [SCRAMBLE_KEY_SIZE-1:0]  key;

      // Pad 32-bit partition data into 128-bit key input
      // Because the mem_q size is a multiple of 64-bit, so if the last round only has 64-bits key,
      // it will repeat the last 64-bits twice
      for (int j = 0; j < key_factor; j++) begin
        int index = i * key_factor + j;
        key |= ((index >= array_size ? mem_q[index-2] : mem_q[index]) << (j * TL_DW));
      end

      // Trigger 32 round of PRESENT encrypt
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data, key, SCRAMBLE_KEY_SIZE == 80,
                                                     enc_array);
      // XOR the previous state into the digest result according to the Davies-Meyer scheme.
      digest = enc_array[NUM_ROUND-1] ^ input_data;
    end

    // Last 32 round of digest is calculated with a digest constant
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(digest,
                                                   RndCnstDigestConst[0],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    digest ^= enc_array[NUM_ROUND-1];

    update_digest_to_otp(part_idx, digest);
  endfunction

  // when secret data write into otp_array, it will be scrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] scramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                      int part_idx);
    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data,
                                                   RndCnstKey[secret_idx],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   output_data);
    scramble_data = output_data[NUM_ROUND-1];
  endfunction

  // when secret data read out of otp_array, it will be descrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] descramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                        int part_idx);
    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] padded_input;

    padded_input[NUM_ROUND-1] = input_data;
    crypto_dpi_present_pkg::sv_dpi_present_decrypt(padded_input,
                                                   RndCnstKey[secret_idx],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   output_data);
    descramble_data = output_data[NUM_ROUND-1];
    if (input_data != 0) begin
    end
  endfunction

  // this function go through present encode algo two or three iterations:
  // first iteration with input key,
  // second iteration with second_key, this iteration only happens if num_round is 2
  // third iteration with a final constant as key
  // this is mainly used for unlock token hashing, key derivation
  virtual function bit [SCRAMBLE_DATA_SIZE-1:0] present_encode_with_final_const(
                                                bit [SCRAMBLE_DATA_SIZE-1:0] data,
                                                bit [SCRAMBLE_KEY_SIZE-1:0]  key,
                                                bit [SCRAMBLE_KEY_SIZE-1:0]  final_const,
                                                bit [SCRAMBLE_KEY_SIZE-1:0]  second_key = '0,
                                                int                          num_round = 1);
    bit [NUM_ROUND-1:0] [SCRAMBLE_DATA_SIZE-1:0] enc_array;
    bit [SCRAMBLE_DATA_SIZE-1:0] intermediate_state;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(data, key, SCRAMBLE_KEY_SIZE == 80, enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    intermediate_state = data ^ enc_array[NUM_ROUND-1];

    if (num_round == 2) begin
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, second_key,
                                                     SCRAMBLE_KEY_SIZE == 80, enc_array);
      intermediate_state = intermediate_state ^ enc_array[NUM_ROUND-1];
    end else if (num_round > 2) begin
      `uvm_fatal(`gfn, $sformatf("does not support num_round: %0d > 2", num_round))
    end

    crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, final_const,
                                                   SCRAMBLE_KEY_SIZE == 80, enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    present_encode_with_final_const = enc_array[NUM_ROUND-1] ^ intermediate_state;
  endfunction

  function bit [TL_AW-1:0] get_scb_otp_addr();
    bit [TL_DW-1:0] dai_addr = `gmv(ral.direct_access_address);
    get_scb_otp_addr = (is_secret(dai_addr) || is_digest(dai_addr)) ? dai_addr >> 3 << 1 :
                                                                      dai_addr >> 2;
  endfunction

  // This function predict OTP error related registers: intr_state, status, and err_code
  virtual function void predict_err(otp_status_e   status_err_idx,
                                    otp_err_code_e err_code = OtpNoError,
                                    bit            update_esc_err = 0);
    if (cfg.otp_ctrl_vif.under_error_states() && !update_esc_err) return;

    // Update intr_state
    void'(ral.intr_state.otp_error.predict(.value(1), .kind(UVM_PREDICT_READ)));
    // Update status
    exp_status[status_err_idx] = 1;

    // Only first 8 status errors have corresponding err_code
    if (status_err_idx <= OtpLciErrIdx) begin
      dv_base_reg_field err_code_flds[$];
      if (err_code == OtpNoError) begin
        `uvm_error(`gfn, $sformatf("please set status error: %0s error code", status_err_idx.name))
      end
      ral.err_code.get_dv_base_reg_fields(err_code_flds);

      if (`gmv(err_code_flds[status_err_idx]) inside {OTP_TERMINAL_ERRS}) begin
        `uvm_info(`gfn, "terminal error cannot be updated", UVM_HIGH)
      end else if (status_err_idx == OtpLciErrIdx &&
                   `gmv(err_code_flds[status_err_idx]) != OtpNoError) begin
        `uvm_info(`gfn, "For LC partition, all errors are terminal error!", UVM_HIGH)
      end else begin
        void'(err_code_flds[status_err_idx].predict(.value(err_code), .kind(UVM_PREDICT_READ)));
      end
    end

  endfunction

  // TODO: consider combine it with function predict_err()
  virtual function void predict_no_err(otp_status_e status_err_idx);
    if (cfg.otp_ctrl_vif.under_error_states()) return;

    exp_status[status_err_idx] = 0;
    if (status_err_idx == OtpDaiErrIdx) exp_status[OtpDaiIdleIdx] = 1;

    if (status_err_idx <= OtpLciErrIdx) begin
      dv_base_reg_field err_code_flds[$];
      ral.err_code.get_dv_base_reg_fields(err_code_flds);
      void'(err_code_flds[status_err_idx].predict(OtpNoError));
    end
  endfunction

  virtual function void predict_rdata(bit is_64_bits, bit [TL_DW-1:0] rdata0,
                                      bit [TL_DW-1:0] rdata1 = 0);
    void'(ral.direct_access_rdata_0.predict(.value(rdata0), .kind(UVM_PREDICT_READ)));
    if (is_64_bits) begin
      void'(ral.direct_access_rdata_1.predict(.value(rdata1), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  // this function retrieves keys (128 bits) from scb's otp_array with a starting address
  // if not locked, it will return 0
  // this is mainly used for scrambling key algo
  virtual function bit [SCRAMBLE_KEY_SIZE-1:0] get_key_from_otp(bit locked, int start_i);
    bit [SCRAMBLE_KEY_SIZE-1:0] key;
    if (!locked) return 0;
    for (int i = 0; i < 4; i++) key |= otp_a[i + start_i] << (TL_DW * i);
    return key;
  endfunction

  // The following two methods are all retrieving digest val.
  // get_otp_digest_val: is the digest value from OTP memory
  // get_digest_reg_val: is the digest value in register. This value is identical to OTP
  // memory's digest value after a power cycle reset.
  virtual function bit [TL_DW*2-1:0] get_otp_digest_val(int part_idx);
    get_otp_digest_val[31:0]  = otp_a[PART_OTP_DIGEST_ADDRS[part_idx]];
    get_otp_digest_val[63:32] = otp_a[PART_OTP_DIGEST_ADDRS[part_idx] + 1];
  endfunction

  virtual function bit [TL_DW*2-1:0] get_digest_reg_val(int part_idx);
    bit [TL_DW*2-1:0] digest;
    case (part_idx)
      CreatorSwCfgIdx: begin
        digest = {`gmv(ral.creator_sw_cfg_digest_1), `gmv(ral.creator_sw_cfg_digest_0)};
      end
      OwnerSwCfgIdx: digest = {`gmv(ral.owner_sw_cfg_digest_1), `gmv(ral.owner_sw_cfg_digest_0)};
      HwCfgIdx: digest = {`gmv(ral.hw_cfg_digest_1), `gmv(ral.hw_cfg_digest_0)};
      Secret0Idx: digest = {`gmv(ral.secret0_digest_1), `gmv(ral.secret0_digest_0)};
      Secret1Idx: digest = {`gmv(ral.secret1_digest_1), `gmv(ral.secret1_digest_0)};
      Secret2Idx: digest = {`gmv(ral.secret2_digest_1), `gmv(ral.secret2_digest_0)};
      default: `uvm_fatal(`gfn, $sformatf("Partition %0d does not have digest", part_idx))
    endcase
    return digest;
  endfunction

  virtual function bit is_tl_mem_access_allowed(tl_seq_item item, string ral_name);
    // If sw partition is read locked, then access policy changes from RO to no access
    uvm_reg_addr_t addr = ral.get_word_aligned_addr(item.a_addr);
    if (`gmv(ral.creator_sw_cfg_read_lock) == 0 || cfg.otp_ctrl_vif.under_error_states()) begin
      if (addr inside {[cfg.mem_ranges[ral_name][0].start_addr :
                       cfg.mem_ranges[ral_name][0].start_addr + CreatorSwCfgSize - 1]}) begin
        predict_err(OtpCreatorSwCfgErrIdx, OtpAccessError);
        `DV_CHECK_EQ(item.d_data, 0,
                     $sformatf("locked mem read mismatch at TLUL addr %0h in CreatorSwCfg", addr))
        return 0;
      end
    end
    if (`gmv(ral.owner_sw_cfg_read_lock) == 0 ||  cfg.otp_ctrl_vif.under_error_states()) begin
      if (addr inside {[cfg.mem_ranges[ral_name][0].start_addr + OwnerSwCfgOffset :
          cfg.mem_ranges[ral_name][0].start_addr + OwnerSwCfgSize + OwnerSwCfgOffset - 1]}) begin
        predict_err(OtpOwnerSwCfgErrIdx, OtpAccessError);
        `DV_CHECK_EQ(item.d_data, 0,
                     $sformatf("locked mem read mismatch at TLUL addr %0h in OwnerSwCfg", addr))
        return 0;
      end
    end
    return super.is_tl_mem_access_allowed(item, ral_name);
  endfunction

  virtual function void set_exp_alert(string alert_name, bit is_fatal = 0, int max_delay = 0);
    exp_alert = alert_name == "fatal_check_error" ? OtpCheckAlert : OtpMacroAlert;
    super.set_exp_alert(alert_name, is_fatal, max_delay);
  endfunction
endclass
