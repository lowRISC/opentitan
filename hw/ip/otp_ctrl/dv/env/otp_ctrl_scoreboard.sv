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

  // LC partition does not have digest
  bit [SCRAMBLE_DATA_SIZE-1:0] digests[NumPart-1];

  // This bit is used for DAI interface to mark if the read access is valid.
  bit dai_read_valid;
  // This two bits are local values stored for sw partitions' read lock registers.
  bit [1:0] sw_read_lock;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(SRAM_DATA_SIZE)))
                        sram_fifo[NumSramKeyReqSlots];
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
      sram_fifo[i] = new($sformatf("sram_fifo[%0d]", i), this);
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
    join_none
  endtask

  virtual task process_backdoor_mem_clear();
    forever begin
      @(posedge cfg.pwr_otp_vif.pins[OtpPwrInitReq]) begin
        if (cfg.backdoor_clear_mem) begin
          bit [SCRAMBLE_DATA_SIZE-1:0] data = descramble_data(0, 0);
          otp_a   = '{default:0};
          digests = '{default:0};
          sw_read_lock = 0;
          // secret partitions have been scrambled before writing to OTP.
          // here calculate the pre-srambled raw data when clearing internal OTP to all 0s.
          for (int i = SECRET0_START_ADDR; i <= SECRET0_END_ADDR; i++) begin
            otp_a[i] = ((i - SECRET0_START_ADDR) % 2) ? data[SCRAMBLE_DATA_SIZE-1:TL_DW] :
                                                        data[TL_DW-1:0];
          end
          data = descramble_data(0, 1);
          for (int i = SECRET1_START_ADDR; i <= SECRET1_END_ADDR; i++) begin
            otp_a[i] = ((i - SECRET1_START_ADDR) % 2) ? data[SCRAMBLE_DATA_SIZE-1:TL_DW] :
                                                        data[TL_DW-1:0];
          end
          data = descramble_data(0, 2);
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
      exp_data_0 = present_encode_with_final_const(.data(RndCnstDigestIVDefault[1]),
                                                   .key(rcv_item.h_data),
                                                   .final_const(RndCnstDigestConstDefault[1]));
      exp_data_1 = present_encode_with_final_const(.data(exp_data_0),
                                                   .key(rcv_item.h_data),
                                                   .final_const(RndCnstDigestConstDefault[1]));
      `DV_CHECK_EQ(rcv_item.d_data, {exp_data_1, exp_data_0}, "lc_token_encode_mismatch")
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
        bit [TL_AW-1:0] dai_addr = (csr_addr & addr_mask - SW_WINDOW_BASE_ADDR) >> 2;
        int part_idx = get_part_index(dai_addr);
        bit [TL_DW-1:0] exp_val = sw_read_lock[part_idx] ? 0 : otp_a[dai_addr];
        `DV_CHECK_EQ(item.d_data, exp_val, $sformatf("mem read mismatch at addr %0h", dai_addr))
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
        if (addr_phase_write && ral.direct_access_regwen.get_mirrored_value()) begin
          // here only normalize to 2 lsb, if is secret, will be reduced further
          bit [TL_AW-1:0] dai_addr = ral.direct_access_address.get_mirrored_value() >> 2 << 2;
          int part_idx = get_part_index(dai_addr);
          case (item.a_data)
            DaiDigest: cal_digest_val(part_idx);
            DaiRead: begin
              // SW partitions write read_lock_csr can lock read access
              // Secret partitions cal digest can also lock read access
              if ((part_idx inside {CreatorSwCfgIdx, OwnerSwCfgIdx} && sw_read_lock[part_idx]) ||
                  (is_secret(dai_addr) && digests[part_idx] != 0)) begin
                predict_status_err(.dai_err(1));
                dai_read_valid = 0;
              end else begin
                void'(ral.status.predict(OtpDaiIdle));
                dai_read_valid = 1;
              end
            end
            DaiWrite: begin
              // check if write locked
              if (digests[part_idx] != 0) begin
                predict_status_err(.dai_err(1));
              end else begin
                void'(ral.status.predict(OtpDaiIdle));
                // write digest
                if (dai_addr inside {CreatorSwCfgDigestOffset, OwnerSwCfgDigestOffset}) begin
                  digests[part_idx] = {ral.direct_access_wdata_1.get_mirrored_value(),
                                       ral.direct_access_wdata_0.get_mirrored_value()};
                // write OTP memory
                end else begin
                  bit[TL_AW-1:0] normalized_dai_addr = get_normalized_dai_addr();
                  otp_a[normalized_dai_addr] = ral.direct_access_wdata_0.get_mirrored_value();
                  if (is_secret(dai_addr)) begin
                    otp_a[normalized_dai_addr + 1] = ral.direct_access_wdata_1.
                                                     get_mirrored_value();
                  end
                  // TODO: LC partition, raise status error
                end
              end
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("invalid cmd: %0d", item.a_data))
            end
          endcase
        end
      end
      "direct_access_rdata_0", "direct_access_rdata_1": begin
        // TODO: need to check last cmd is READ
        if (data_phase_read && ral.direct_access_regwen.get_mirrored_value()) begin
          bit [TL_AW-1:0] dai_addr = get_normalized_dai_addr();
          if (csr.get_name() == "direct_access_rdata_0") begin
            bit [TL_DW-1:0] exp_val = dai_read_valid ? otp_a[dai_addr] : 0;
            `DV_CHECK_EQ(item.d_data, exp_val,
                         $sformatf("DAI read mismatch at addr %0h", dai_addr))
            do_read_check = 0;
          end else begin
            if (is_secret(ral.direct_access_address.get_mirrored_value())) begin
              bit [TL_DW-1:0] exp_val = dai_read_valid ? otp_a[dai_addr + 1] : 0;
              `DV_CHECK_EQ(item.d_data, exp_val,
                           $sformatf("DAI read mismatch at addr %0h", dai_addr + 1))
              do_read_check = 0;
            end
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
      "direct_access_wdata_1", "direct_access_address", "status": begin
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
    void'(ral.status.predict(OtpDaiIdle));
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
    bit [SCRAMBLE_DATA_SIZE-1:0]                 init_vec = RndCnstDigestIVDefault[0];
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
        scrambled_data = scramble_data({mem_q[i*2+1], mem_q[i*2]}, part_idx - Secret0Idx);
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
      digests[part_idx] = enc_array[NUM_ROUND-1];
    end

    // Last 32 round of digest is calculated with a digest constant
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(digests[part_idx],
                                                   RndCnstDigestConstDefault[0],
                                                   key_size_80,
                                                   enc_array);
    digests[part_idx] = enc_array[NUM_ROUND-1];
  endfunction

  // when secret data write into otp_array, it will be scrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] scramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                      int secret_idx);
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data,
                                                   RndCnstKeyDefault[secret_idx],
                                                   key_size_80,
                                                   output_data);
    scramble_data = output_data[NUM_ROUND-1];
  endfunction

  // when secret data read out of otp_array, it will be descrambled
  function bit [SCRAMBLE_DATA_SIZE-1:0] descramble_data(bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
                                                        int secret_idx);
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_decrypt(input_data,
                                                   RndCnstKeyDefault[secret_idx],
                                                   key_size_80,
                                                   output_data);
    descramble_data = output_data[NUM_ROUND-1];
  endfunction

  // this function go through present encode algo twice:
  // one with input key, one with a final constant
  // this is mainly used for unlock token hashing
  virtual function bit [SCRAMBLE_DATA_SIZE-1:0] present_encode_with_final_const(
                                                bit [SCRAMBLE_DATA_SIZE-1:0] data,
                                                bit [SCRAMBLE_KEY_SIZE-1:0]  key,
                                                bit [SCRAMBLE_KEY_SIZE-1:0]  final_const);
    bit [NUM_ROUND-1:0] [SCRAMBLE_DATA_SIZE-1:0] enc_array;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(data, key, key_size_80, enc_array);
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(enc_array[NUM_ROUND-1], final_const,
                                                   key_size_80, enc_array);
    present_encode_with_final_const = enc_array[NUM_ROUND-1];
  endfunction

  function bit [TL_AW-1:0] get_normalized_dai_addr();
    bit [TL_DW-1:0] dai_addr = ral.direct_access_address.get_mirrored_value();
    get_normalized_dai_addr = is_secret(dai_addr) ? dai_addr >> 3 << 1 : dai_addr >> 2;
  endfunction

  virtual function void predict_status_err(bit dai_err, int part_idx = 0);
    void'(ral.intr_state.otp_error.predict(.value(1)));
    if (dai_err) void'(ral.status.predict(OtpDaiErr | OtpDaiIdle));
  endfunction
endclass
