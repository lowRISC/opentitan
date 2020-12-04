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
  bit [TL_DW-1:0] hw_cfg_a [HW_CFG_ARRAY_SIZE];

  // LC partition does not have digest
  bit [SCRAMBLE_DATA_SIZE-1:0] digests[NumPart-1];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(SRAM_DATA_SIZE)))  sram_fifo[NumSramKeyReqSlots];
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(OTBN_DATA_SIZE)))  otbn_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_addr_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(FLASH_DATA_SIZE))) flash_data_fifo;
  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(EDN_DATA_SIZE)))   edn_fifo;

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
    edn_fifo        = new("edn_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_backdoor_mem_clear();
    join_none
  endtask

  virtual task process_backdoor_mem_clear();
    forever begin
      @(posedge cfg.pwr_otp_vif.pins[OtpPwrInitReq]) begin
        if (cfg.backdoor_clear_mem) begin
          hw_cfg_a = '{default:0};
          digests  = '{default:0};
          predict_digest_csrs();
          `uvm_info(`gfn, "clear internal memory and digest", UVM_HIGH)
        end
      end
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check     = 1'b0;
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
    // memories
    // TODO: memory read check, change hardcoded to parameters once design finalized
    end else if ((csr_addr & addr_mask) inside
        {[SW_WINDOW_BASE_ADDR : SW_WINDOW_BASE_ADDR + SW_WINDOW_SIZE],
         [TEST_ACCESS_BASE_ADDR : TEST_ACCESS_BASE_ADDR + TEST_ACCESS_WINDOW_SIZE]}) begin
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
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "direct_access_cmd": begin
        if (addr_phase_write && ral.direct_access_regwen.get_mirrored_value()) begin
          int dai_addr = ral.direct_access_address.get_mirrored_value();
          case (item.a_data)
            DaiDigest: begin
              // TODO: temp if statement, take away when support all partitions
              if (get_part_index(dai_addr) == HwCfgIdx) begin
                cal_digest_val(HwCfgIdx);
              end
            end
            DaiWrite: begin
              if (get_part_index(dai_addr) == HwCfgIdx) begin
                int cal_addr = (dai_addr - HwCfgOffset) >> 2;
                hw_cfg_a[cal_addr] = ral.direct_access_wdata_0.get_mirrored_value();
              end
            end
          endcase
        end
      end
      // TODO: temp only enable this checking, should support all regs
      "hw_cfg_digest_0": do_read_check = 1;
      "hw_cfg_digest_1": do_read_check = 1;
      default: begin
        //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
        // TODO: temp disable check, right now only support hw_cfg_digest
        do_read_check = 0;
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    // digest values are updated after a power cycle
    predict_digest_csrs();
  endfunction

  // predict digest registers
  virtual function void predict_digest_csrs();
    void'(ral.hw_cfg_digest_0.predict(.value(digests[HwCfgIdx][31:0]),
                                      .kind(UVM_PREDICT_DIRECT)));
    void'(ral.hw_cfg_digest_1.predict(.value(digests[HwCfgIdx][63:32]),
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
    bit [TL_DW-1:0] mem_q[$];
    int             array_size;
    int             key_factor  = SCRAMBLE_KEY_SIZE / TL_DW;
    bit             key_size_80 = SCRAMBLE_KEY_SIZE == 80;

    // TODO: currently only support HwCfg partition
    case (part_idx)
      HwCfgIdx: begin
        array_size = HW_CFG_ARRAY_SIZE;
        mem_q = hw_cfg_a;
      end
    endcase

    for (int i = 0; i <= $ceil(array_size / key_factor); i++) begin
      bit [SCRAMBLE_DATA_SIZE-1:0] input_data = (i == 0) ? RndCnstDigestIVDefault[0] :
                                                           digests[part_idx];
      bit [SCRAMBLE_KEY_SIZE-1:0] key;

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
endclass
