// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_comment}
<%
from topgen.lib import Name

read_locked_csr_parts = [part for part in otp_mmap.config["partitions"] if
                         part["read_lock"] == "CSR"]
write_locked_digest_parts = [part for part in otp_mmap.config["partitions"] if
                             part["write_lock"] == "Digest"]
buf_parts_without_lc = [part for part in otp_mmap.config["partitions"] if
                        part["variant"] == "Buffered"]
secret_parts = [part for part in otp_mmap.config["partitions"] if
                part["secret"]]
## Partitions + LCI + DAI
num_err_code = len(otp_mmap.config["partitions"]) + 2
%>\
class otp_ctrl_scoreboard #(type CFG_T = otp_ctrl_env_cfg)
  extends cip_base_scoreboard #(
    .CFG_T(CFG_T),
    .RAL_T(otp_ctrl_core_reg_block),
    .COV_T(otp_ctrl_env_cov)
  );
  `uvm_component_param_utils(otp_ctrl_scoreboard #(CFG_T))

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

  // This captures the regwen state as configured by the SW side (i.e. without HW modulation
  // with the idle signal overlaid).
  bit direct_access_regwen_state = 1;

  // ICEBOX(#17798): currently scb will skip checking the readout value if the ECC error is
  // uncorrectable. Because if the error is uncorrectable, current scb does not track all the
  // backdoor injected values.
  // This issue proposes to track the otp_memory_array in mem_bkdr_if and once backdoor inject any
  // value, mem_bkdr_if will update its otp_memory_array.
  bit check_dai_rd_data = 1;

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
      process_wipe_mem();
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

  // Once sequence uses backdoor method to clear memory, this task resets internal otp_a and
  // resets `cfg.backdoor_clear_mem` to 0.
  virtual task process_wipe_mem();
    forever begin
      @(posedge cfg.backdoor_clear_mem) begin
        bit [SCRAMBLE_DATA_SIZE-1:0] data;
        otp_a        = '{default:0};
        otp_lc_data  = '{default:0};
% for part in secret_parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
        // secret partitions have been scrambled before writing to OTP.
        // here calculate the pre-srambled raw data when clearing internal OTP to all 0s.
        data = descramble_data(0, ${part_name_camel}Idx);
        for (int i = ${part_name_camel}Offset / TL_SIZE;
             i <= ${part_name_camel}DigestOffset / TL_SIZE - 1;
             i++) begin
          otp_a[i] = ((i - ${part_name_camel}Offset / TL_SIZE) % 2) ?
              data[SCRAMBLE_DATA_SIZE-1:TL_DW] : data[TL_DW-1:0];
        end
% endfor
        `uvm_info(`gfn, "clear internal memory and digest", UVM_HIGH)
        cfg.backdoor_clear_mem = 0;
        dai_wr_ip = 0;
        dai_digest_ip = LifeCycleIdx;
      end
    end
  endtask

  // This task process the following logic in during otp_power_up:
  // 1. After reset deasserted, otp access is locked until pwr_otp_done_o is set
  // 2. After reset deasserted, if power otp_init request is on, and if testbench uses backdoor to
  //    clear OTP memory to all zeros, clear all digests and re-calculate secret partitions
  virtual task process_otp_power_up();
    forever begin
      wait (cfg.en_scb);
      @(posedge cfg.otp_ctrl_vif.pwr_otp_done_o || cfg.under_reset ||
                cfg.otp_ctrl_vif.alert_reqs) begin
        if (!cfg.under_reset && !cfg.otp_ctrl_vif.alert_reqs && cfg.en_scb) begin
          otp_ctrl_part_pkg::otp_hw_cfg0_data_t  exp_hw_cfg0_data;
          otp_ctrl_part_pkg::otp_hw_cfg1_data_t  exp_hw_cfg1_data;
          otp_ctrl_pkg::otp_keymgr_key_t         exp_keymgr_data;
          otp_ctrl_pkg::otp_lc_data_t            exp_lc_data;
          bit [otp_ctrl_pkg::KeyMgrKeyWidth-1:0] exp_keymgr_key0, exp_keymgr_key1;

          if (PartInfo[dai_digest_ip].sw_digest || PartInfo[dai_digest_ip].hw_digest) begin
            bit [TL_DW-1:0] otp_addr = PART_OTP_DIGEST_ADDRS[dai_digest_ip];
            otp_a[otp_addr]   = cfg.mem_bkdr_util_h.read32(otp_addr << 2);
            otp_a[otp_addr+1] = cfg.mem_bkdr_util_h.read32((otp_addr << 2) + 4);
            dai_digest_ip = LifeCycleIdx;
          end
          predict_digest_csrs();

          if (cfg.otp_ctrl_vif.under_error_states() == 0) begin
            // Dai access is unlocked because the power init is done
            void'(ral.direct_access_regwen.predict(direct_access_regwen_state));

            // Dai idle is set because the otp init is done
            exp_status[OtpDaiIdleIdx] = 1;
          end

          // Hwcfg_o gets data from OTP HW cfg partition
          exp_hw_cfg0_data = cfg.otp_ctrl_vif.under_error_states() ?
                             otp_ctrl_part_pkg::PartInvDefault[HwCfg0Offset*8 +: HwCfg0Size*8] :
                             otp_hw_cfg0_data_t'({<<32 {otp_a[HwCfg0Offset/4 +: HwCfg0Size/4]}});
          `DV_CHECK_EQ(cfg.otp_ctrl_vif.otp_broadcast_o.valid, lc_ctrl_pkg::On)
          `DV_CHECK_EQ(cfg.otp_ctrl_vif.otp_broadcast_o.hw_cfg0_data, exp_hw_cfg0_data)

          // Hwcfg_o gets data from OTP HW cfg partition
          exp_hw_cfg1_data = cfg.otp_ctrl_vif.under_error_states() ?
                             otp_ctrl_part_pkg::PartInvDefault[HwCfg1Offset*8 +: HwCfg1Size*8] :
                             otp_hw_cfg1_data_t'({<<32 {otp_a[HwCfg1Offset/4 +: HwCfg1Size/4]}});
          `DV_CHECK_EQ(cfg.otp_ctrl_vif.otp_broadcast_o.valid, lc_ctrl_pkg::On)
          `DV_CHECK_EQ(cfg.otp_ctrl_vif.otp_broadcast_o.hw_cfg1_data, exp_hw_cfg1_data)

          if (!cfg.otp_ctrl_vif.under_error_states()) begin
            // ---------------------- Check lc_data_o output -----------------------------------
            // Because initialization was succesful, the valid should be set and error should be
            // reset.
            exp_lc_data.valid = 1;
            exp_lc_data.error = 0;

            // Secrets and tokens valid signals are depend on whether secret partitions are
            // locked.
            exp_lc_data.secrets_valid = get_otp_digest_val(Secret2Idx) ? On : Off;
            exp_lc_data.test_tokens_valid = get_otp_digest_val(Secret0Idx) ? On : Off;
            exp_lc_data.rma_token_valid = get_otp_digest_val(Secret2Idx) ? On : Off;

            // LC output is depend on LC partitions value.
            exp_lc_data.count = otp_lc_data[0 +: LcCountWidth];
            exp_lc_data.state = otp_lc_data[LcCountWidth +: LcStateWidth];

            // Token values are depend on secret partitions value.
            exp_lc_data.test_unlock_token =
                    {<<32 {otp_a[TestUnlockTokenOffset/4 +: TestUnlockTokenSize/4]}};
            exp_lc_data.test_exit_token =
                    {<<32 {otp_a[TestExitTokenOffset/4 +: TestExitTokenSize/4]}};
            exp_lc_data.rma_token = {<<32 {otp_a[RmaTokenOffset/4 +: RmaTokenSize/4]}};

            // Check otp_lc_data_t struct by item is easier to debug.
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.valid, exp_lc_data.valid)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.error, exp_lc_data.error)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.state, exp_lc_data.state)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.count, exp_lc_data.count)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.secrets_valid, exp_lc_data.secrets_valid)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.test_tokens_valid,
                         exp_lc_data.test_tokens_valid)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.test_unlock_token,
                         exp_lc_data.test_unlock_token)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.test_exit_token, exp_lc_data.test_exit_token)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.rma_token_valid, exp_lc_data.rma_token_valid)
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o.rma_token, exp_lc_data.rma_token)

            // Check otp_lc_data_t all together in case there is any missed item.
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.lc_data_o, exp_lc_data)

            // ---------------------- Check keymgr_key_o output ---------------------------------
            // Otp_keymgr outputs creator and owner keys from secret partitions.
            // Depends on lc_seed_hw_rd_en_i, it will output the real keys or a constant
            exp_keymgr_data = '0;
% for part in otp_mmap.config["partitions"]:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
  % if part["iskeymgr_creator"] or part["iskeymgr_owner"]:
    % for item in part["items"]:
<%
  item_name = Name.from_snake_case(item["name"])
  item_name_camel = item_name.as_camel_case()
%>\
      % if item["iskeymgr_creator"] or item["iskeymgr_owner"]:
            exp_keymgr_data.${item["name"].lower()}_valid = get_otp_digest_val(${part_name_camel}Idx) != 0;
            if (cfg.otp_ctrl_vif.lc_seed_hw_rd_en_i == lc_ctrl_pkg::On) begin
              exp_keymgr_data.${item["name"].lower()} =
                  {<<32 {otp_a[${item_name_camel}Offset/4 +: ${item_name_camel}Size/4]}};
            end else begin
              exp_keymgr_data.${item["name"].lower()} =
                  PartInvDefault[${item_name_camel}Offset*8 +: ${item_name_camel}Size*8];
            end
            // Check otp_keymgr_key_t struct by item is easier to debug.
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.keymgr_key_o.${item["name"].lower()}_valid,
                         exp_keymgr_data.${item["name"].lower()}_valid)
      % endif
    % endfor
  % endif
% endfor

            // Check otp_keymgr_key_t struct all together in case there is any missed item.
            `DV_CHECK_EQ(cfg.otp_ctrl_vif.keymgr_key_o, exp_keymgr_data)

            if (cfg.en_cov) begin
              cov.keymgr_o_cg.sample(cfg.otp_ctrl_vif.lc_seed_hw_rd_en_i == lc_ctrl_pkg::On,
                                     exp_keymgr_data.creator_root_key_share0_valid);
            end
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
      foreach (FATAL_EXP_STATUS[i]) begin
        if (FATAL_EXP_STATUS[i]) begin
          predict_err(.status_err_idx(otp_status_e'(i)), .err_code(OtpFsmStateError),
                      .update_esc_err(1));
        end
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
      wait(cfg.otp_ctrl_vif.lc_prog_req == 1);
      wait(cfg.otp_ctrl_vif.lc_prog_req == 0);
      // Wait one 1ps to avoid race condition.
      #1ps;
      if (cfg.otp_ctrl_vif.rst_ni == 0) begin
        for (int i = 0; i < LC_PROG_DATA_SIZE/32; i++) begin
          otp_lc_data[i*32+:32] = cfg.mem_bkdr_util_h.read32(LifeCycleOffset + i * 4);
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
      edn_fifos[0].get(edn_item);
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
      part_locked = {`gmv(ral.secret1_digest[0]), `gmv(ral.secret1_digest[1])} != '0;

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
      automatic digest_sel_e sel_flash = digest_sel_e'(i);
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
          part_locked = {`gmv(ral.secret1_digest[0]), `gmv(ral.secret1_digest[1])} != '0;
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
          nonce      = rcv_item.d_data[1+:SramNonceWidth];
          key        = rcv_item.d_data[SramNonceWidth+1+:SramKeyWidth];
          part_locked = {`gmv(ral.secret1_digest[0]), `gmv(ral.secret1_digest[1])} != '0;

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
    bit         write         = item.is_write();
    uvm_reg_addr_t csr_addr   = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] addr_mask = ral.get_addr_mask();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    if (ral_name != "otp_ctrl_prim_reg_block") begin
      process_core_tl_access(item, csr_addr, ral_name, addr_mask,
                             addr_phase_read, addr_phase_write, data_phase_read, data_phase_write);
    end else begin
      process_prim_tl_access(item, csr_addr, ral_name, addr_phase_write, data_phase_read);
    end
  endtask

  virtual function void process_prim_tl_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
      string ral_name, bit addr_phase_write, bit data_phase_read);

    uvm_reg     csr;
    dv_base_reg dv_reg;
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
    `downcast(dv_reg, csr)

    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end else if (data_phase_read) begin
      `DV_CHECK_EQ((csr.get_mirrored_value() | status_mask), (item.d_data | status_mask),
                   $sformatf("reg name: status, compare_mask %0h", status_mask))
    end
  endfunction

  virtual function void process_core_tl_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
      string ral_name, bit [TL_AW-1:0] addr_mask, bit addr_phase_read, bit addr_phase_write,
      bit data_phase_read, bit data_phase_write);

    bit         do_read_check = 1;
    uvm_reg     csr;
    dv_base_reg dv_reg;
    string      csr_name;

    `uvm_info(`gfn, $sformatf("sw state %d, reg state %d", direct_access_regwen_state,
                             `gmv(ral.direct_access_regwen)), UVM_LOW);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_reg, csr)
    // SW CFG window
    end else if ((csr_addr & addr_mask) inside
        {[SW_WINDOW_BASE_ADDR : SW_WINDOW_BASE_ADDR + SW_WINDOW_SIZE]}) begin
      if (data_phase_read) begin
        bit [TL_AW-1:0] dai_addr = (csr_addr & addr_mask - SW_WINDOW_BASE_ADDR);
        bit [TL_AW-1:0] otp_addr = dai_addr >> 2;
        int part_idx = get_part_index(dai_addr);
        bit [TL_DW-1:0] read_out;
        int ecc_err = OtpNoEccErr;

        // We can't get an ECC error if the partition does not have integrity.
        if (part_has_integrity(part_idx)) begin
          ecc_err = read_a_word_with_ecc(dai_addr, read_out);
        end else begin
          ecc_err = read_a_word_with_ecc_raw(dai_addr, read_out);
        end

        if (part_has_digest(part_idx) && cfg.en_cov) begin
          cov.unbuf_access_lock_cg_wrap[part_idx].sample(.read_lock(0),
              .write_lock(get_digest_reg_val(part_idx) != 0), .is_write(0));
        end

        // Any alert that indicates the OTP block is in the final error state should not enter the
        // logic here, but gated at `is_tl_mem_access_allowed` function.
        `DV_CHECK_EQ(cfg.otp_ctrl_vif.alert_reqs, 0)

        // ECC uncorrectable errors are gated by `is_tl_mem_access_allowed` function.
        if (ecc_err != OtpNoEccErr && part_has_integrity(part_idx)) begin

          predict_err(otp_status_e'(part_idx), OtpMacroEccCorrError);
          if (ecc_err == OtpEccCorrErr) begin
             `DV_CHECK_EQ(item.d_data, otp_a[otp_addr],
                         $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
                         csr_addr, dai_addr))
          end else begin
            // Only check the first 16 bits because if ECC readout detects uncorrectable error, it
            // won't continue read the remaining 16 bits.
            `DV_CHECK_EQ(item.d_data & 16'hffff, read_out & 16'hffff,
                       $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
                       csr_addr, dai_addr))
          end
        // If there is an injected error, but the partition cannot detect it, we have to compare
        // to the value read via the backdoor instead of otp_a[otp_addr] since otherwise the
        // perturbed value does not get modelled correctly.
        end else if (ecc_err != OtpNoEccErr && !part_has_integrity(part_idx)) begin
          `DV_CHECK_EQ(item.d_data, read_out,
                      $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
                      csr_addr, dai_addr))
          predict_no_err(otp_status_e'(part_idx));
        end else if (ecc_err == OtpNoEccErr) begin
          `DV_CHECK_EQ(item.d_data, otp_a[otp_addr],
                      $sformatf("mem read mismatch at TLUL addr %0h, csr_addr %0h",
                      csr_addr, dai_addr))
          predict_no_err(otp_status_e'(part_idx));
        end
      end
      return;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    csr_name = csr.get_name();

    if (addr_phase_write) begin
      if (cfg.en_cov && cfg.otp_ctrl_vif.alert_reqs && csr_name == "direct_access_cmd") begin
        cov.req_dai_access_after_alert_cg.sample(item.a_data);
      end

      // Skip predict if the register is locked by `direct_access_regwen`.
      // An exception is the direct_access_regwen which may always be written.
      if (ral.direct_access_regwen.locks_reg_or_fld(dv_reg) &&
          `gmv(ral.direct_access_regwen) == 0 &&
          csr_name != "direct_access_regwen") return;

      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
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
          bit [TL_AW-1:0] dai_addr = normalize_dai_addr(`gmv(ral.direct_access_address));
          int part_idx = get_part_index(dai_addr);
          bit sw_read_lock = 0;
          void'(ral.direct_access_regwen.predict(0));
          under_dai_access = 1;

          // Check if it is sw partition read lock - this can be used in `DaiRead` branch and also
          // coverage collection.
% for part in read_locked_csr_parts:
<% part_name = Name.from_snake_case(part["name"]) %>\
  % if loop.first:
          if (part_idx == ${part_name.as_camel_case()}Idx) begin
  % else:
          end else if (part_idx == ${part_name.as_camel_case()}Idx) begin
  % endif
            sw_read_lock = `gmv(ral.${part_name.as_snake_case()}_read_lock) == 0;
  % if loop.last:
          end
  %endif
% endfor

          // LC partition cannot be access via DAI
          if (part_idx == LifeCycleIdx) begin
            predict_err(OtpDaiErrIdx, OtpAccessError);
            if (item.a_data == DaiRead) predict_rdata(is_secret(dai_addr), 0, 0);
          end else begin
            // Collect coverage.
            if (cfg.en_cov) begin
              if (part_idx == Secret2Idx) begin
                cov.dai_access_secret2_cg.sample(
                    !(cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i != lc_ctrl_pkg::On),
                    dai_cmd_e'(item.a_data));
              end else if (is_sw_part_idx(part_idx) && part_has_digest(part_idx) &&
                           item.a_data inside {DaiRead, DaiWrite}) begin
                cov.unbuf_access_lock_cg_wrap[part_idx].sample(.read_lock(sw_read_lock),
                    .write_lock(get_digest_reg_val(part_idx) != 0),
                    .is_write(item.a_data == DaiWrite));

              end
            end

            case (item.a_data)
              DaiDigest: cal_digest_val(part_idx);
              DaiRead: begin
                // Check if it is sw partition read lock
                check_dai_rd_data = 1;

                // SW partitions write read_lock_csr can lock read access.
                if (sw_read_lock ||
                    // Secret partitions cal digest can also lock read access.
                    // However, digest is always readable except SW partitions (Issue #5752).
                    (is_secret(dai_addr) && get_digest_reg_val(part_idx) != 0 &&
                     !is_digest(dai_addr)) ||
                    // If the partition has creator key material and lc_creator_seed_sw_rw is
                    // disable, then return access error.
                    (PartInfo[part_idx].iskeymgr_creator && !is_digest(dai_addr) &&
                     cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i != lc_ctrl_pkg::On)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                  predict_rdata(is_secret(dai_addr) || is_digest(dai_addr), 0, 0);
                end else if (sw_read_lock ||
                    // Secret partitions cal digest can also lock read access.
                    // However, digest is always readable except SW partitions (Issue #5752).
                    (is_secret(dai_addr) && get_digest_reg_val(part_idx) != 0 &&
                     !is_digest(dai_addr)) ||
                    // If the partition has owner key material and lc_owner_seed_sw_rw is disable,
                    // then return access error.
                    (PartInfo[part_idx].iskeymgr_owner && !is_digest(dai_addr) &&
                     cfg.otp_ctrl_vif.lc_owner_seed_sw_rw_en_i != lc_ctrl_pkg::On)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                  predict_rdata(is_secret(dai_addr) || is_digest(dai_addr), 0, 0);

                end else begin
                  bit [TL_DW-1:0] read_out0, read_out1;
                  bit [TL_AW-1:0] otp_addr = get_scb_otp_addr();
                  int ecc_err = 0;

                  // Backdoor read to check if there is any ECC error.
                  if (part_has_integrity(part_idx)) begin
                    ecc_err = read_a_word_with_ecc(dai_addr, read_out0);
                    if (is_secret(dai_addr) || is_digest(dai_addr)) begin
                      ecc_err = max2(read_a_word_with_ecc(dai_addr + 4, read_out1), ecc_err);
                    end
                  end else begin
                    ecc_err = read_a_word_with_ecc_raw(dai_addr, read_out0);
                    if (is_secret(dai_addr) || is_digest(dai_addr)) begin
                      ecc_err = max2(read_a_word_with_ecc_raw(dai_addr + 4, read_out1), ecc_err);
                    end
                  end

                  if (ecc_err == OtpEccCorrErr && part_has_integrity(part_idx)) begin
                    predict_err(OtpDaiErrIdx, OtpMacroEccCorrError);
                    backdoor_update_otp_array(dai_addr);
                    predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                  otp_a[otp_addr], otp_a[otp_addr+1]);
                  end else if (ecc_err == OtpEccUncorrErr && part_has_integrity(part_idx)) begin
                    predict_err(OtpDaiErrIdx, OtpMacroEccUncorrError);
                    // Max wait 20 clock cycles because scb did not know when exactly OTP will
                    // finish reading and reporting the uncorrectable error.
                    set_exp_alert("fatal_macro_error", 1, 20);
                    predict_rdata(1, 0, 0);
                  // Some partitions do not interpret/report ECC errors. In those cases
                  // we still need to model the read data correctly if it has been perturbed.
                  end else if (ecc_err inside {OtpEccCorrErr, OtpEccUncorrErr} &&
                               !part_has_integrity(part_idx)) begin
                    predict_no_err(OtpDaiErrIdx);
                    predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                  read_out0, read_out1);
                    // do not check direct_access_rdata_* on ECC errors in
                    // non-integrity partitions
                    check_dai_rd_data = 0;
                  end else begin
                    predict_no_err(OtpDaiErrIdx);
                    predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                  otp_a[otp_addr], otp_a[otp_addr+1]);
                  end
                end
              end
              DaiWrite: begin
                bit[TL_AW-1:0] otp_addr = get_scb_otp_addr();
                bit is_write_locked;
                // check if write locked
                if (part_has_digest(part_idx)) begin
                  is_write_locked = get_digest_reg_val(part_idx) != 0;
                end else begin
                  is_write_locked = 0;
                end

                if (is_write_locked || (PartInfo[part_idx].iskeymgr_creator &&
                    !is_digest(dai_addr) &&
                    cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i != lc_ctrl_pkg::On)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                end else if (is_write_locked || (PartInfo[part_idx].iskeymgr_owner &&
                             !is_digest(dai_addr) &&
                             cfg.otp_ctrl_vif.lc_owner_seed_sw_rw_en_i != lc_ctrl_pkg::On)) begin
                  predict_err(OtpDaiErrIdx, OtpAccessError);
                end else begin
                  predict_no_err(OtpDaiErrIdx);
                  // write digest
                  if (is_sw_digest(dai_addr)) begin
                    bit [TL_DW*2-1:0] curr_digest, prev_digest;
                    curr_digest = {`gmv(ral.direct_access_wdata[1]),
                                   `gmv(ral.direct_access_wdata[0])};
                    prev_digest = {otp_a[otp_addr+1], otp_a[otp_addr]};
                    dai_wr_ip = 1;
                    // allow bit write
                    if ((prev_digest & curr_digest) == prev_digest) begin
                      update_digest_to_otp(part_idx, curr_digest);
                    end else begin
                      predict_err(OtpDaiErrIdx, OtpMacroWriteBlankError);
                    end
                  end else if (is_digest(dai_addr)) begin
                    predict_err(OtpDaiErrIdx, OtpAccessError);
                  // write OTP memory
                  end else begin
                    dai_wr_ip = 1;
                    if (!is_secret(dai_addr)) begin
                      bit [TL_DW-1:0] wr_data = `gmv(ral.direct_access_wdata[0]);
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
                      bit [SCRAMBLE_DATA_SIZE-1:0] wr_data = {`gmv(ral.direct_access_wdata[1]),
                                                              `gmv(ral.direct_access_wdata[0])};
                      wr_data = scramble_data(wr_data, part_idx);
                      secret_data = scramble_data(secret_data, part_idx);
                      if ((secret_data & wr_data) == secret_data) begin
                        otp_a[otp_addr]     = `gmv(ral.direct_access_wdata[0]);
                        otp_a[otp_addr + 1] = `gmv(ral.direct_access_wdata[1]);
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
          if (cfg.en_cov) begin
            cov.collect_status_cov(item.d_data);
            if (cfg.otp_ctrl_vif.alert_reqs) begin
              cov.csr_rd_after_alert_cg_wrap.sample(csr.get_offset());
            end
          end

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
              void'(ral.direct_access_regwen.predict(direct_access_regwen_state));
              void'(ral.intr_state.otp_operation_done.predict(1));
            end
          end
        end
        // checked in this block above
        do_read_check = 0;
      end
      "check_trigger": begin
        if (addr_phase_write && cfg.en_cov && cfg.otp_ctrl_vif.alert_reqs) begin
          cov.issue_checks_after_alert_cg.sample(item.a_data);
        end

        if (addr_phase_write && `gmv(ral.check_trigger_regwen) && item.a_data inside {[1:3]}) begin
          bit [TL_DW-1:0] check_timeout = `gmv(ral.check_timeout) == 0 ? '1 :
                                                                        `gmv(ral.check_timeout);
          exp_status[OtpCheckPendingIdx] = 1;
          under_chk = 1;
          if (check_timeout <= CHK_TIMEOUT_CYC) begin
            set_exp_alert("fatal_check_error", 1, `gmv(ral.check_timeout));
            predict_err(OtpTimeoutErrIdx);
          end else begin
            if (get_field_val(ral.check_trigger.consistency, item.a_data)) begin
              foreach (cfg.ecc_chk_err[i]) begin
                if (cfg.ecc_chk_err[i] == OtpEccCorrErr && part_has_integrity(i)) begin
                  predict_err(otp_status_e'(i), OtpMacroEccCorrError);
                end else if (cfg.ecc_chk_err[i] == OtpEccUncorrErr &&
                             part_has_integrity(i)) begin
                  set_exp_alert("fatal_macro_error", 1, 40_000);
                  predict_err(otp_status_e'(i), OtpMacroEccUncorrError);
                end
              end
            end
          end
        end
      end
      "direct_access_regwen": begin
        if (addr_phase_write) begin
          // This locks the DAI until the next reset.
          if (!item.a_data[0]) begin
            direct_access_regwen_state = 0;
            void'(ral.direct_access_regwen.predict(0));
          end
        end
      end
      // For error codes, if lc_prog in progress, err_code might update anytime in DUT. Ignore
      // checking until req is acknowledged.

% for k in range(num_err_code):
<%
  # This code should depend on whether the error code is compact. This
  # assumes it is not compact.
%>\
      "err_code_${k}": begin
        if (cfg.m_lc_prog_pull_agent_cfg.vif.req) do_read_check = 0;
        if (cfg.en_cov && do_read_check && data_phase_read) begin
          bit [TL_DW-1:0] dai_addr = `gmv(ral.direct_access_address) >> 2 << 2;
          int access_part_idx = get_part_index(dai_addr);
          cov.collect_err_code_cov(${k}, item.d_data, access_part_idx);
        end
      end
% endfor
% for part in write_locked_digest_parts:
<% part_name_snake = Name.from_snake_case(part["name"]).as_snake_case() %>\
      "${part_name_snake}_digest_0", "${part_name_snake}_digest_1"${": begin" if loop.last else ","}
% endfor
        if (ignore_digest_chk) do_read_check = 0;
      end
% for part in read_locked_csr_parts:
<% part_name_snake = Name.from_snake_case(part["name"]).as_snake_case() %>\
      "${part_name_snake}_read_lock",
% endfor
      "direct_access_wdata_0",
      "direct_access_wdata_1",
      "direct_access_address",
      "check_regwen",
      "check_trigger_regwen",
      "check_trigger",
      "check_timeout",
      "intr_enable",
      "integrity_check_period",
      "consistency_check_period",
      "alert_test": begin
        // Do nothing
      end
      // DAI read data
      "direct_access_rdata_0", "direct_access_rdata_1": do_read_check = check_dai_rd_data;
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
        if (cfg.en_cov && cfg.otp_ctrl_vif.alert_reqs) begin
          cov.csr_rd_after_alert_cg_wrap.sample(csr.get_offset());
        end
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  // If reset or lc_escalate_en is issued during otp program, this function will backdoor update
  // otp memory write value because scb did not know how many cells haven been written.
  // We won't update csr `direct_access_address` after fatal alert happened, so in this function
  // we can directly call method `get_scb_otp_addr` to get the interrupted dai address.
  virtual function void recover_interrupted_op();
    if (dai_wr_ip) begin
      bit [TL_DW-1:0] otp_addr = get_scb_otp_addr();
      bit [TL_DW-1:0] dai_addr = otp_addr << 2;
      backdoor_update_otp_array(dai_addr);
      dai_wr_ip = 0;
    end
  endfunction

  virtual function void backdoor_update_otp_array(bit [TL_DW-1:0] dai_addr);
    bit [TL_DW-1:0] otp_addr = dai_addr >> 2;
    bit [TL_DW-1:0] readout_word, readout_word1;
    int part_idx = get_part_index(dai_addr);
    if (part_has_integrity(part_idx)) begin
      void'(read_a_word_with_ecc(dai_addr,     readout_word));
      void'(read_a_word_with_ecc(dai_addr + 4, readout_word1));
    end else begin
      void'(read_a_word_with_ecc_raw(dai_addr,     readout_word));
      void'(read_a_word_with_ecc_raw(dai_addr + 4, readout_word1));
    end

    otp_a[otp_addr] = readout_word;

    if (is_digest(dai_addr)) begin
      otp_a[otp_addr+1] = readout_word1;
    end else if (is_secret(dai_addr)) begin
      bit [TL_DW*2-1:0] mem_rd_val, descrambled_val;
      mem_rd_val        = {readout_word1 ,readout_word};
      descrambled_val   = descramble_data(mem_rd_val, part_idx);
      otp_a[otp_addr+1] = descrambled_val[TL_DW*2-1:TL_DW];
      otp_a[otp_addr]   = descrambled_val[TL_DW-1:0];
    end
  endfunction

  virtual function bit [1:0] read_a_word_with_ecc(bit [TL_DW-1:0] dai_addr,
                                                  ref bit [TL_DW-1:0] readout_word);
    prim_secded_pkg::secded_22_16_t ecc_rd_data0 = cfg.mem_bkdr_util_h.ecc_read16(dai_addr);
    prim_secded_pkg::secded_22_16_t ecc_rd_data1 = cfg.mem_bkdr_util_h.ecc_read16(dai_addr + 2);
    readout_word[15:0]  = ecc_rd_data0.data;
    readout_word[31:16] = ecc_rd_data1.data;
    return max2(ecc_rd_data0.err, ecc_rd_data1.err);
  endfunction

  // Returns the ECC error but does not correct the data bits (i.e. returns the raw data).
  virtual function bit [1:0] read_a_word_with_ecc_raw(bit [TL_DW-1:0] dai_addr,
                                                     ref bit [TL_DW-1:0] readout_word);
    prim_secded_pkg::secded_22_16_t ecc_rd_data0 = cfg.mem_bkdr_util_h.ecc_read16(dai_addr);
    prim_secded_pkg::secded_22_16_t ecc_rd_data1 = cfg.mem_bkdr_util_h.ecc_read16(dai_addr + 2);
    readout_word[15:0]  = 16'hFFFF & cfg.mem_bkdr_util_h.read(dai_addr);
    readout_word[31:16] = 16'hFFFF & cfg.mem_bkdr_util_h.read(dai_addr + 2);
    return max2(ecc_rd_data0.err, ecc_rd_data1.err);
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

    direct_access_regwen_state = 1;
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
                 cfg.m_sram_pull_agent_cfg[2].vif.req ||
                 cfg.m_sram_pull_agent_cfg[3].vif.req ||
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
% for part in write_locked_digest_parts:
<% part_name = Name.from_snake_case(part["name"]) %>\
    void'(ral.${part_name.as_snake_case()}_digest[0].predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[${part_name.as_camel_case()}Idx]]),
          .kind(UVM_PREDICT_DIRECT)));
    void'(ral.${part_name.as_snake_case()}_digest[1].predict(
          .value(otp_a[PART_OTP_DIGEST_ADDRS[${part_name.as_camel_case()}Idx] + 1]),
          .kind(UVM_PREDICT_DIRECT)));
  % if not loop.last:

  %endif
% endfor
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
    bit [TL_DW-1:0]              mem_q[$];
    int                          array_size;
    bit [SCRAMBLE_DATA_SIZE-1:0] digest;

    if (cfg.otp_ctrl_vif.under_error_states()) return;

    if (!part_has_hw_digest(part_idx) || get_digest_reg_val(part_idx) != 0) begin
      predict_err(OtpDaiErrIdx, OtpAccessError);
      return;
    end else if (PartInfo[part_idx].iskeymgr_creator &&
                 cfg.otp_ctrl_vif.lc_creator_seed_sw_rw_en_i != lc_ctrl_pkg::On) begin
      predict_err(OtpDaiErrIdx, OtpAccessError);
      return;
    end else if (PartInfo[part_idx].iskeymgr_owner &&
                 cfg.otp_ctrl_vif.lc_owner_seed_sw_rw_en_i != lc_ctrl_pkg::On) begin
      predict_err(OtpDaiErrIdx, OtpAccessError);
      return;
    end else begin
      predict_no_err(OtpDaiErrIdx);
      dai_digest_ip = part_idx;
    end
    case (part_idx)
% for part in buf_parts_without_lc:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
      ${part_name_camel}Idx: mem_q = otp_a[${part_name_camel}Offset / TL_SIZE : ${part_name_camel}DigestOffset / TL_SIZE - 1];
% endfor
      default: begin
        `uvm_fatal(`gfn, $sformatf("Access unexpected partition %0d", part_idx))
      end
    endcase

    array_size = mem_q.size();

    // for secret partitions, need to use otp scrambled value as data input
    if (PartInfo[part_idx].secret) begin
      bit [TL_DW-1:0] scrambled_mem_q[$];
      for (int i = 0; i < array_size/2; i++) begin
        bit [SCRAMBLE_DATA_SIZE-1:0] scrambled_data;
        scrambled_data = scramble_data({mem_q[i*2+1], mem_q[i*2]}, part_idx);
        scrambled_mem_q.push_back(scrambled_data[TL_DW-1:0]);
        scrambled_mem_q.push_back(scrambled_data[SCRAMBLE_DATA_SIZE-1:TL_DW]);
      end
      mem_q = scrambled_mem_q;
    end

    digest = otp_scrambler_pkg::cal_digest(part_idx, mem_q);
    update_digest_to_otp(part_idx, digest);
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
    bit [SCRAMBLE_DATA_SIZE-1:0] enc_data;
    bit [SCRAMBLE_DATA_SIZE-1:0] intermediate_state;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(data, key,
                                                   SCRAMBLE_KEY_SIZE, NUM_ROUND, enc_data);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    intermediate_state = data ^ enc_data;

    if (num_round == 2) begin
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, second_key,
                                                     SCRAMBLE_KEY_SIZE, NUM_ROUND, enc_data);
      intermediate_state = intermediate_state ^ enc_data;
    end else if (num_round > 2) begin
      `uvm_fatal(`gfn, $sformatf("does not support num_round: %0d > 2", num_round))
    end

    crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, final_const,
                                                   SCRAMBLE_KEY_SIZE, NUM_ROUND, enc_data);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    present_encode_with_final_const = intermediate_state ^ enc_data;
  endfunction

  // Get address for scoreboard's otp_a array from the `direct_access_address` CSR
  function bit [TL_DW-1:0] get_scb_otp_addr();
    bit [TL_DW-1:0] dai_addr = `gmv(ral.direct_access_address);
    get_scb_otp_addr = normalize_dai_addr(dai_addr) >> 2;
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

    // Only first status errors up to the LCI have corresponding err_code
    if (status_err_idx <= OtpLciErrIdx) begin
      dv_base_reg_field err_code_flds[$];
      if (err_code == OtpNoError) begin
        `uvm_error(`gfn, $sformatf("please set status error: %0s error code", status_err_idx.name))
      end
      ral.err_code[status_err_idx].get_dv_base_reg_fields(err_code_flds);

      if (`gmv(err_code_flds[0]) inside {OTP_TERMINAL_ERRS}) begin
        `uvm_info(`gfn, "terminal error cannot be updated", UVM_HIGH)
      end else if (status_err_idx == OtpLciErrIdx &&
                   `gmv(err_code_flds[0]) != OtpNoError) begin
        `uvm_info(`gfn, "For LC partition, all errors are terminal error!", UVM_HIGH)
      end else begin
        void'(err_code_flds[0].predict(.value(err_code), .kind(UVM_PREDICT_READ)));
      end
    end

  endfunction

  virtual function void predict_no_err(otp_status_e status_err_idx);
    if (cfg.otp_ctrl_vif.under_error_states()) return;

    exp_status[status_err_idx] = 0;
    if (status_err_idx == OtpDaiErrIdx) exp_status[OtpDaiIdleIdx] = 1;

    if (status_err_idx <= OtpLciErrIdx) begin
      dv_base_reg_field err_code_flds[$];
      ral.err_code[status_err_idx].get_dv_base_reg_fields(err_code_flds);
      void'(err_code_flds[0].predict(OtpNoError));
    end
  endfunction

  virtual function void predict_rdata(bit is_64_bits, bit [TL_DW-1:0] rdata0,
                                      bit [TL_DW-1:0] rdata1 = 0);
    void'(ral.direct_access_rdata[0].predict(.value(rdata0), .kind(UVM_PREDICT_READ)));
    if (is_64_bits) begin
      void'(ral.direct_access_rdata[1].predict(.value(rdata1), .kind(UVM_PREDICT_READ)));
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
% for part in write_locked_digest_parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_snake = part_name.as_snake_case()
%>\
      ${part_name.as_camel_case()}Idx: begin
        digest = {`gmv(ral.${part_name_snake}_digest[1]),
                  `gmv(ral.${part_name_snake}_digest[0])};
      end
% endfor
      default: `uvm_fatal(`gfn, $sformatf("Partition %0d does not have digest", part_idx))
    endcase
    return digest;
  endfunction

  virtual function bit is_tl_mem_access_allowed(input tl_seq_item item, input string ral_name,
                                                output bit mem_byte_access_err,
                                                output bit mem_wo_err,
                                                output bit mem_ro_err,
                                                output bit custom_err);

    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    uvm_reg_addr_t csr_addr   = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] addr_mask = ral.get_addr_mask();
    bit [TL_AW-1:0] dai_addr = (csr_addr & addr_mask - SW_WINDOW_BASE_ADDR);

    bit mem_access_allowed = super.is_tl_mem_access_allowed(item, ral_name, mem_byte_access_err,
                                                            mem_wo_err, mem_ro_err, custom_err);

    if (ral_name == "otp_ctrl_prim_reg_block") return mem_access_allowed;

    // Ensure the address is within the memory window range.
    // Also will skip checking if memory access is not allowed due to TLUL bus error.
    if (addr inside {
        [cfg.ral_models[ral_name].mem_ranges[0].start_addr :
         cfg.ral_models[ral_name].mem_ranges[0].end_addr]} &&
        mem_access_allowed) begin

      // If sw partition is read locked, then access policy changes from RO to no access
% for part in read_locked_csr_parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
      if (`gmv(ral.${part_name.as_snake_case()}_read_lock) == 0 ||
          cfg.otp_ctrl_vif.under_error_states()) begin
        if (addr inside {
            [cfg.ral_models[ral_name].mem_ranges[0].start_addr + ${part_name_camel}Offset :
             cfg.ral_models[ral_name].mem_ranges[0].start_addr + ${part_name_camel}Offset +
             ${part_name_camel}Size - 1]}) begin
          predict_err(Otp${part_name_camel}ErrIdx, OtpAccessError);
          custom_err = 1;
          if (cfg.en_cov) begin
  % if part["write_lock"] == "Digest":
            cov.unbuf_access_lock_cg_wrap[${part_name_camel}Idx].sample(.read_lock(1),
                .write_lock(get_digest_reg_val(${part_name_camel}Idx) != 0), .is_write(0));
  % else:
            // TODO: we should probably create a different covergroup
            // for unbuffered partitions without digest.
            cov.unbuf_access_lock_cg_wrap[${part_name_camel}Idx].sample(.read_lock(1),
                .write_lock(0), .is_write(0));
  % endif
          end
          return 0;
        end
      end
% endfor

      // Check ECC uncorrectable fatal error.
      if (dai_addr < LifeCycleOffset) begin
        int part_idx = get_part_index(dai_addr);
        bit [TL_DW-1:0] read_out;
        int ecc_err = read_a_word_with_ecc(dai_addr, read_out);
        if (ecc_err == OtpEccUncorrErr && part_has_integrity(part_idx)) begin
           predict_err(otp_status_e'(part_idx), OtpMacroEccUncorrError);
           set_exp_alert("fatal_macro_error", 1, 20);
           custom_err = 1;
           return 0;
        end
      end
    end

    return mem_access_allowed;
  endfunction

  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    if (ral_name == "otp_ctrl_prim_reg_block" &&
        cfg.otp_ctrl_vif.lc_dft_en_i != lc_ctrl_pkg::On) begin
      if (channel == DataChannel) begin
        `DV_CHECK_EQ(item.d_error, 1,
            $sformatf({"On interface %0s, TL item: %0s, access gated by lc_dft_en_i"},
            ral_name, item.sprint(uvm_default_line_printer)))

        // In data read phase, check d_data when d_error = 1.
        if (item.d_error && (item.d_opcode == tlul_pkg::AccessAckData)) begin
          check_tl_read_value_after_error(item, ral_name);
        end
      end
      return 1;
    end
    return super.predict_tl_err(item, channel, ral_name);
  endfunction

  virtual function void set_exp_alert(string alert_name, bit is_fatal = 0, int max_delay = 0);
    exp_alert = alert_name == "fatal_check_error" ? OtpCheckAlert : OtpMacroAlert;
    super.set_exp_alert(alert_name, is_fatal, max_delay);
  endfunction

endclass
