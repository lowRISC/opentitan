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
  bit key_size_80 = SCRAMBLE_KEY_SIZE == 80;
  bit [EDN_BUS_WIDTH-1:0] edn_data_q[$];

  // LC partition does not have digest
  bit [SCRAMBLE_DATA_SIZE-1:0] digests[NumPart-1];

  // This bit is used for DAI interface to mark if the read access is valid.
  bit dai_read_valid;
  // This two bits are local values stored for sw partitions' read lock registers.
  bit [1:0] sw_read_lock;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(SRAM_DATA_SIZE)))
                        sram_fifos[NumSramKeyReqSlots];
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(OTBN_DATA_SIZE)))  otbn_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_addr_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_data_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE)))
                        lc_prog_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth)))
                        lc_token_fifo;

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
    lc_token_fifo   = new("lc_token_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_backdoor_mem_clear();
      process_lc_token_req();
      process_edn_req();
      check_otbn_rsp();
      check_flash_rsps();
      check_sram_rsps();
    join_none
  endtask

  virtual task process_backdoor_mem_clear();
    forever begin
      @(posedge cfg.otp_ctrl_vif.pwr_otp_init_i && cfg.en_scb) begin
        if (cfg.backdoor_clear_mem) begin
          bit [SCRAMBLE_DATA_SIZE-1:0] data = descramble_data(0, Secret0Idx);
          otp_a   = '{default:0};
          digests = '{default:0};
          sw_read_lock = 0;
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
    end
  endtask

  virtual task process_lc_token_req();
    forever begin
      push_pull_item#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth)) rcv_item;
      bit [SCRAMBLE_DATA_SIZE-1:0] exp_data_0, exp_data_1;
      lc_token_fifo.get(rcv_item);
      exp_data_0 = present_encode_with_final_const(
                   .data(RndCnstDigestIV[LcRawDigest]),
                   .key(rcv_item.h_data),
                   .final_const(RndCnstDigestConst[LcRawDigest]));
      exp_data_1 = present_encode_with_final_const(
                   .data(exp_data_0),
                   .key(rcv_item.h_data),
                   .final_const(RndCnstDigestConst[LcRawDigest]));
      `DV_CHECK_EQ(rcv_item.d_data, {exp_data_1, exp_data_0}, "lc_token_encode_mismatch")
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

      // get edn CSRNG
      `DV_CHECK_EQ(edn_data_q.size(), 16);
      {exp_nonce, edn_key2, edn_key1} = {<<32{edn_data_q}};
      edn_data_q.delete();

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

          // get edn CSRNG
          `DV_CHECK_EQ(edn_data_q.size(), 10);
          {exp_nonce, edn_key2, edn_key1} = {<<32{edn_data_q}};
          edn_data_q.delete();

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
        end
      join_none
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check     = 1'b1;
    bit     write             = item.is_write();
    uvm_reg_addr_t csr_addr   = ral.get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] addr_mask = ral.get_addr_mask();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    // SW CFG window
    end else if ((csr_addr & addr_mask) inside
        {[SW_WINDOW_BASE_ADDR : SW_WINDOW_BASE_ADDR + SW_WINDOW_SIZE]}) begin
      if (data_phase_read) begin
        bit [TL_AW-1:0] otp_addr = (csr_addr & addr_mask - SW_WINDOW_BASE_ADDR) >> 2;
        int part_idx = get_part_index(otp_addr << 2);
        bit [TL_DW-1:0] exp_val = sw_read_lock[part_idx] ? 0 : otp_a[otp_addr];
        `DV_CHECK_EQ(item.d_data, exp_val,
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

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        do_read_check = 1'b0;
        // FIXME
      end
      "intr_test": begin
        do_read_check = 1'b0;
        // FIXME
      end
      "direct_access_cmd": begin
        if (addr_phase_write && `gmv(ral.direct_access_regwen)) begin
          // here only normalize to 2 lsb, if is secret, will be reduced further
          bit [TL_AW-1:0] dai_addr = `gmv(ral.direct_access_address) >> 2 << 2;
          int part_idx = get_part_index(dai_addr);
          // LC partition cannot be access via DAI
          if (part_idx == LifeCycleIdx) begin
            predict_status_err(.dai_err(1));
            if (item.a_data == DaiRead) predict_rdata(is_secret(dai_addr), 0, 0);
          end else begin
            case (item.a_data)
              DaiDigest: cal_digest_val(part_idx);
              DaiRead: begin
                // SW partitions write read_lock_csr can lock read access
                // Secret partitions cal digest can also lock read access
                // However, digest is always readable
                if ((part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx} && sw_read_lock[part_idx]) ||
                    (is_secret(dai_addr) && digests[part_idx] != 0) && !is_digest(dai_addr)) begin
                  predict_status_err(.dai_err(1));
                  predict_rdata(is_secret(dai_addr), 0, 0);
                end else begin
                  bit [TL_AW-1:0] otp_addr = get_scb_otp_addr();
                  predict_rdata(is_secret(dai_addr) || is_digest(dai_addr),
                                otp_a[otp_addr], otp_a[otp_addr+1]);
                  void'(ral.status.predict(OtpDaiIdle));
                end
              end
              DaiWrite: begin
                bit[TL_AW-1:0] otp_addr = get_scb_otp_addr();
                // check if write locked
                if (get_digest_reg_val(part_idx) != 0) begin
                  predict_status_err(.dai_err(1));
                end else begin
                  void'(ral.status.predict(OtpDaiIdle));
                  // write digest
                  if (is_sw_digest(dai_addr)) begin
                    if (otp_a[otp_addr] == 0 && otp_a[otp_addr+1] == 0) begin
                      digests[part_idx] = {`gmv(ral.direct_access_wdata_1),
                                           `gmv(ral.direct_access_wdata_0)};
                      // sw digest directly write to OTP, so reading out digest val do not need to
                      // wait a reset
                      update_sw_digests_to_otp(part_idx);
                    end else begin
                      predict_status_err(.dai_err(1));
                    end
                  end else if (is_digest(dai_addr)) begin
                    predict_status_err(1);
                  // write OTP memory
                  end else begin
                    if (!is_secret(dai_addr)) begin
                      bit [TL_DW-1:0] wr_data = `gmv(ral.direct_access_wdata_0);
                      // allow bit write
                      if ((otp_a[otp_addr] & wr_data) == otp_a[otp_addr]) otp_a[otp_addr] = wr_data;
                      else predict_status_err(1);
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
                      end else begin
                        predict_status_err(1);
                      end
                    end
                  end
                end
              end
              default: begin
                `uvm_fatal(`gfn, $sformatf("invalid cmd: %0d", item.a_data))
              end
            endcase
          end
        end
      end
      "creator_sw_cfg_read_lock": begin
        if (item.d_data == 1) sw_read_lock[CreatorSwCfgIdx] = 1;
      end
      "owner_sw_cfg_read_lock": begin
        if (item.d_data == 1) sw_read_lock[OwnerSwCfgIdx] = 1;
      end
      "hw_cfg_digest_0", "hw_cfg_digest_1", "", "secret0_digest_0", "secret0_digest_1",
      "secret1_digest_0", "secret1_digest_1", "secret2_digest_0", "secret2_digest_1",
      "creator_sw_cfg_digest_0", "creator_sw_cfg_digest_1", "owner_sw_cfg_digest_0",
      "owner_sw_cfg_digest_1", "direct_access_regwen", "direct_access_wdata_0",
      "direct_access_wdata_1", "direct_access_address", "direct_access_rdata_0",
      "direct_access_rdata_1", "status": begin
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

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    // digest values are updated after a power cycle
    predict_digest_csrs();
    update_digests_to_otp_mem();
    void'(ral.status.predict(OtpDaiIdle));
    edn_data_q.delete();
  endfunction

  // predict digest registers
  virtual function void predict_digest_csrs();
    void'(ral.creator_sw_cfg_digest_0.predict(.value(digests[CreatorSwCfgIdx][31:0]),
                                              .kind(UVM_PREDICT_DIRECT)));
    void'(ral.creator_sw_cfg_digest_1.predict(.value(digests[CreatorSwCfgIdx][63:32]),
                                              .kind(UVM_PREDICT_DIRECT)));
    void'(ral.owner_sw_cfg_digest_0.predict(.value(digests[OwnerSwCfgIdx][31:0]),
                                            .kind(UVM_PREDICT_DIRECT)));
    void'(ral.owner_sw_cfg_digest_1.predict(.value(digests[OwnerSwCfgIdx][63:32]),
                                            .kind(UVM_PREDICT_DIRECT)));
    void'(ral.hw_cfg_digest_0.predict(.value(digests[HwCfgIdx][31:0]),
                                      .kind(UVM_PREDICT_DIRECT)));
    void'(ral.hw_cfg_digest_1.predict(.value(digests[HwCfgIdx][63:32]),
                                      .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret0_digest_0.predict(.value(digests[Secret0Idx][31:0]),
                                       .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret0_digest_1.predict(.value(digests[Secret0Idx][63:32]),
                                       .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret1_digest_0.predict(.value(digests[Secret1Idx][31:0]),
                                       .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret1_digest_1.predict(.value(digests[Secret1Idx][63:32]),
                                       .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret2_digest_0.predict(.value(digests[Secret2Idx][31:0]),
                                       .kind(UVM_PREDICT_DIRECT)));
    void'(ral.secret2_digest_1.predict(.value(digests[Secret2Idx][63:32]),
                                       .kind(UVM_PREDICT_DIRECT)));
  endfunction

  function void update_sw_digests_to_otp(int part_idx);
    if (part_idx == CreatorSwCfgIdx) begin
      otp_a[CreatorSwCfgDigestOffset >> 2]       = digests[CreatorSwCfgIdx][31:0];
      otp_a[(CreatorSwCfgDigestOffset >> 2) + 1] = digests[CreatorSwCfgIdx][63:32];
    end else begin
      otp_a[OwnerSwCfgDigestOffset >> 2]         = digests[OwnerSwCfgIdx][31:0];
      otp_a[(OwnerSwCfgDigestOffset >> 2) + 1]   = digests[OwnerSwCfgIdx][63:32];
    end
  endfunction

  function void update_digests_to_otp_mem();
    update_sw_digests_to_otp(CreatorSwCfgIdx);
    update_sw_digests_to_otp(OwnerSwCfgIdx);

    otp_a[HwCfgDigestOffset >> 2]         = digests[HwCfgIdx][31:0];
    otp_a[(HwCfgDigestOffset >> 2) + 1]   = digests[HwCfgIdx][63:32];
    otp_a[Secret0DigestOffset >> 2]       = digests[Secret0Idx][31:0];
    otp_a[(Secret0DigestOffset >> 2) + 1] = digests[Secret0Idx][63:32];
    otp_a[Secret1DigestOffset >> 2]       = digests[Secret1Idx][31:0];
    otp_a[(Secret1DigestOffset >> 2) + 1] = digests[Secret1Idx][63:32];
    otp_a[Secret2DigestOffset >> 2]       = digests[Secret2Idx][31:0];
    otp_a[(Secret2DigestOffset >> 2) + 1] = digests[Secret2Idx][63:32];
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
    bit [TL_DW-1:0] mem_q[$];
    int             array_size;
    real            key_factor  = SCRAMBLE_KEY_SIZE / TL_DW;

    if (digests[part_idx] != 0 ||
        part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx, LifeCycleIdx}) begin
      predict_status_err(.dai_err(1));
      return;
    end else begin
      void'(ral.status.predict(OtpDaiIdle));
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
      bit [SCRAMBLE_DATA_SIZE-1:0] input_data = (i == 0) ? init_vec : digests[part_idx];
      bit [SCRAMBLE_KEY_SIZE-1:0]  key;

      // Pad 32-bit partition data into 128-bit key input
      // Because the mem_q size is a multiple of 64-bit, so if the last round only has 64-bits key,
      // it will repeat the last 64-bits twice
      for (int j = 0; j < key_factor; j++) begin
        int index = i * key_factor + j;
        key |= ((index >= array_size ? mem_q[index-2] : mem_q[index]) << (j * TL_DW));
      end

      // Trigger 32 round of PRESENT encrypt
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data, key, key_size_80, enc_array);
      // XOR the previous state into the digest result according to the Davies-Meyer scheme.
      digests[part_idx] = enc_array[NUM_ROUND-1] ^ input_data;
    end

    // Last 32 round of digest is calculated with a digest constant
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(digests[part_idx],
                                                   RndCnstDigestConst[0],
                                                   key_size_80,
                                                   enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    digests[part_idx] ^= enc_array[NUM_ROUND-1];
  endfunction

  // when secret data write into otp_array, it will be scrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] scramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                      int part_idx);
    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data,
                                                   RndCnstKey[secret_idx],
                                                   key_size_80,
                                                   output_data);
    scramble_data = output_data[NUM_ROUND-1];
  endfunction

  // when secret data read out of otp_array, it will be descrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] descramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                        int part_idx);
    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_decrypt(input_data,
                                                   RndCnstKey[secret_idx],
                                                   key_size_80,
                                                   output_data);
    descramble_data = output_data[NUM_ROUND-1];
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
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(data, key, key_size_80, enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    intermediate_state = data ^ enc_array[NUM_ROUND-1];

    if (num_round == 2) begin
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, second_key,
                                                     key_size_80, enc_array);
      intermediate_state = intermediate_state ^ enc_array[NUM_ROUND-1];
    end else if (num_round > 2) begin
      `uvm_fatal(`gfn, $sformatf("does not support num_round: %0d > 2", num_round))
    end

    crypto_dpi_present_pkg::sv_dpi_present_encrypt(intermediate_state, final_const,
                                                   key_size_80, enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    present_encode_with_final_const = enc_array[NUM_ROUND-1] ^ intermediate_state;
  endfunction

  function bit [TL_AW-1:0] get_scb_otp_addr();
    bit [TL_DW-1:0] dai_addr = `gmv(ral.direct_access_address);
    get_scb_otp_addr = (is_secret(dai_addr) || is_digest(dai_addr)) ? dai_addr >> 3 << 1 :
                                                                      dai_addr >> 2;
  endfunction

  virtual function void predict_status_err(bit dai_err, int part_idx = 0);
    void'(ral.intr_state.otp_error.predict(.value(1)));
    if (dai_err) void'(ral.status.predict(OtpDaiErr | OtpDaiIdle));
  endfunction

  virtual function void predict_rdata(bit is_64_bits, bit [TL_DW-1:0] rdata0,
                                      bit [TL_DW-1:0] rdata1 = 0);
    void'(ral.direct_access_rdata_0.predict(rdata0));
    if (is_64_bits) void'(ral.direct_access_rdata_1.predict(rdata1));
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

endclass
