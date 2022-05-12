// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_base_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_sw_base_vseq)

  // Default only iterate through SW code once.
  constraint num_trans_c {
    num_trans == 1;
  }

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Disable mem checks in scoreboard - it does not factor in memory scrambling.
    cfg.en_scb_mem_chk = 1'b0;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // Reset the sw_test_status.
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  // Backdoor load the sw test image, setup UART, logger and test status interfaces.
  virtual task cpu_init();
     int size_bytes;
     int total_bytes;

    `uvm_info(`gfn, "Started cpu_init", UVM_MEDIUM)
    // TODO: Fixing this for now - need to find a way to pass this on to the SW test.
    foreach (cfg.m_uart_agent_cfgs[i]) begin
      cfg.m_uart_agent_cfgs[i].set_parity(1'b0, 1'b0);
      cfg.m_uart_agent_cfgs[i].set_baud_rate(cfg.uart_baud_rate);
    end

    // initialize the sw logger interface
    foreach (cfg.sw_images[i]) begin
      cfg.sw_logger_vif.add_sw_log_db(cfg.sw_images[i]);
    end
    cfg.sw_logger_vif.sw_log_addr = SW_DV_LOG_ADDR;
    cfg.sw_logger_vif.write_sw_logs_to_file = cfg.write_sw_logs_to_file;
    cfg.sw_logger_vif.ready();

    // initialize the sw test status
    cfg.sw_test_status_vif.sw_test_status_addr = SW_DV_TEST_STATUS_ADDR;

    `uvm_info(`gfn, "Initializing RAM", UVM_MEDIUM)

    // Assume each tile contains the same number of bytes
    size_bytes = cfg.mem_bkdr_util_h[chip_mem_e'(RamMain0)].get_size_bytes();
    total_bytes = size_bytes * cfg.num_ram_main_tiles;

    // Randomize the main SRAM.
    for (int addr = 0; addr < total_bytes; addr = addr + 4) begin
      bit [31:0] rand_val;

      `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val, "Randomization failed!")
      main_sram_bkdr_write32(addr, rand_val);
    end

    // Initialize the data partition in all flash banks to all 1s.
    `uvm_info(`gfn, "Initializing flash banks (data partition only)", UVM_MEDIUM)
    cfg.mem_bkdr_util_h[FlashBank0Data].set_mem();
    cfg.mem_bkdr_util_h[FlashBank1Data].set_mem();

    // Randomize retention memory.  This is done intentionally with wrong integrity
    // as early portions of mask ROM will initialize it to the correct value.
    // The randomization here is just to ensure we do not have x's in the memory.
    for (int ram_idx = 0; ram_idx < cfg.num_ram_ret_tiles; ram_idx++) begin
       cfg.mem_bkdr_util_h[RamRet0 + ram_idx].randomize_mem();
    end

    `uvm_info(`gfn, "Initializing ROM", UVM_MEDIUM)
    // Backdoor load memories with sw images.
    cfg.mem_bkdr_util_h[Rom].load_mem_from_file({cfg.sw_images[SwTypeRom], ".scr.39.vmem"});

    // TODO: the location of the main execution image should be randomized to either bank in future.
    if (cfg.sw_images.exists(SwTypeTest)) begin
      if (cfg.use_spi_load_bootstrap) begin
        `uvm_info(`gfn, "Initializing SPI flash bootstrap", UVM_MEDIUM)
        spi_device_load_bootstrap({cfg.sw_images[SwTypeTest], ".frames.vmem"});
      end else begin
        cfg.mem_bkdr_util_h[FlashBank0Data].load_mem_from_file(
            {cfg.sw_images[SwTypeTest], ".64.scr.vmem"});
      end
    end
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusBooted;

    config_jitter();

    `uvm_info(`gfn, "CPU_init done", UVM_MEDIUM)
  endtask

  task config_jitter();
    bit en_jitter;
    void'($value$plusargs("en_jitter=%0d", en_jitter));
    if (en_jitter) begin
      bit [7:0] en_jitter_arr[] = {1};
      sw_symbol_backdoor_overwrite("kJitterEnabled", en_jitter_arr, Rom, SwTypeRom);
    end
  endtask

  virtual function void main_sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key = RndCnstSramCtrlMainSramKey,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce = RndCnstSramCtrlMainSramNonce);
    _sram_bkdr_write32(addr, data, 1, key, nonce);
  endfunction

  virtual function void ret_sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key = RndCnstSramCtrlRetAonSramKey,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce = RndCnstSramCtrlRetAonSramNonce);
    _sram_bkdr_write32(addr, data, 0, key, nonce);
  endfunction

  // scrambled address may cross the tile, this function will find out what tile the address is
  // located and backdoor write to it.
  protected virtual function void _sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit is_main_ram, // if 1, main ram, otherwise, ret ram
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce);

    chip_mem_e mem;
    int        num_tiles;
    bit [31:0] addr_scr;
    bit [38:0] data_scr;
    bit [31:0] addr_mask;
    int        tile_idx;
    int        size_bytes;

    // Use the 1st tile of the RAM for now. Based on the scrambled address, will find out which
    // tile to write.
    if (is_main_ram) begin
      mem = RamMain0;
      num_tiles = cfg.num_ram_main_tiles;
    end else begin
      mem = RamRet0;
      num_tiles = cfg.num_ram_ret_tiles;
    end

    // Assume each tile contains the same number of bytes
    size_bytes = cfg.mem_bkdr_util_h[mem].get_size_bytes();
    addr_mask = size_bytes - 1;

    // calculate the scramble address
    addr_scr = cfg.mem_bkdr_util_h[mem].get_sram_encrypt_addr(
        addr, nonce, $clog2(num_tiles));

    // determine which tile the scrambled address belongs
    tile_idx = addr_scr / size_bytes;

    // calculate the scrambled data
    data_scr = cfg.mem_bkdr_util_h[mem].get_sram_encrypt32_intg_data(
        addr, data, key, nonce,
        $clog2(num_tiles));

    // write the scrambled data into the targetted memory tile
    mem = chip_mem_e'(mem + tile_idx);
    cfg.mem_bkdr_util_h[mem].write39integ(addr_scr & addr_mask, data_scr);
  endfunction

  virtual task body();
    cfg.sw_test_status_vif.set_num_iterations(num_trans);
    // Initialize the CPU to kick off the sw test.
    cpu_init();
  endtask

  virtual task post_start();
    super.post_start();
    // Wait for sw test to finish before exiting.
    wait_for_sw_test_done();
  endtask

  // Monitors the SW test status.
  virtual task wait_for_sw_test_done();
    `uvm_info(`gfn, "Waiting for the SW test to finish", UVM_MEDIUM)
    fork
      begin: isolation_thread
        fork
          wait(cfg.sw_test_status_vif.sw_test_done);
          #(cfg.sw_test_timeout_ns * 1ns);
        join_any
        disable fork;
        log_sw_test_status();
      end: isolation_thread
    join
  endtask

  // Print pass / fail message to the log.
  virtual function void log_sw_test_status();
    case (cfg.sw_test_status_vif.sw_test_status)
      SwTestStatusPassed: `uvm_info(`gfn, "SW TEST PASSED!", UVM_LOW)
      SwTestStatusFailed: `uvm_error(`gfn, "SW TEST FAILED!")
      default: begin
        // If the SW test has not reached the passed / failed state, then it timed out.
        `uvm_error(`gfn, $sformatf("SW TEST TIMED OUT. STATE: %0s, TIMEOUT = %0d ns\n",
            cfg.sw_test_status_vif.sw_test_status.name(), cfg.sw_test_timeout_ns))
      end
    endcase
  endfunction

  virtual task spi_device_load_bootstrap(string sw_image);
    spi_host_seq m_spi_host_seq;
    byte sw_byte_q[$];
    uint byte_cnt;
    uint num_frame;

    // wait until spi init is done
    // TODO, in some cases though, we might use UART logger instead of SW logger - need to keep that
    // in mind
    wait(cfg.sw_logger_vif.printed_log == "HW initialisation completed, waiting for SPI input...");

    // for the first frame of data, sdo from chip is unknown, ignore checking that
    cfg.m_spi_agent_cfg.en_monitor_checks = 0;

    read_sw_frames(sw_image, sw_byte_q);

    `DV_CHECK_EQ_FATAL((sw_byte_q.size % SPI_FRAME_BYTE_SIZE), 0,
                       "SPI data isn't aligned with frame size")

    while (sw_byte_q.size > byte_cnt) begin
      `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
      for (int i = byte_cnt; i < SPI_FRAME_BYTE_SIZE; i++) begin
        `uvm_info(`gfn, $sformatf("SPI flash data[%0d] = 0x%0x", i, sw_byte_q[i]), UVM_LOW)
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                     data.size() == SPI_FRAME_BYTE_SIZE;
                                     foreach (data[i]) {data[i] == sw_byte_q[byte_cnt+i];})
      `uvm_send(m_spi_host_seq)
      wait (cfg.sw_logger_vif.printed_log == $sformatf("Frame #%0d processed done", num_frame));
      num_frame++;

      byte_cnt += SPI_FRAME_BYTE_SIZE;
    end
  endtask

  virtual function void read_sw_frames(string sw_image, ref byte sw_byte_q[$]);
    int num_returns;
    int mem_fd = $fopen(sw_image, "r");
    bit [31:0] word_data[7];
    string addr;

    while (!$feof(mem_fd)) begin
      num_returns = $fscanf(mem_fd, "%s %h %h %h %h %h %h %h", addr, word_data[0], word_data[1],
                            word_data[2], word_data[3], word_data[4], word_data[5], word_data[6]);
      if (num_returns <= 1) continue;
      for (int i = 0; i < num_returns - 1; i++) begin
        repeat (4) begin
          sw_byte_q.push_back(word_data[i][7:0]);
          word_data[i] = word_data[i] >> 8;
        end
      end
    end
    $fclose(mem_fd);
  endfunction

  // Backdoor-override a const symbol in SW to modify the behavior of the test.
  //
  // In the extended test vseq, override the cpu_init() to add this function call.
  // TODO: bootstrap mode not supported.
  // TODO: Need to deal with scrambling.
  virtual function void sw_symbol_backdoor_overwrite(input string symbol,
                                                     inout bit [7:0] data[],
                                                     input chip_mem_e mem = FlashBank0Data,
                                                     input sw_type_e sw_type = SwTypeTest);

    bit [bus_params_pkg::BUS_AW-1:0] addr, mem_addr;
    uint size;
    uint addr_mask;

    // Elf file name checks.
    `DV_CHECK_FATAL(cfg.sw_images.exists(sw_type))
    `DV_CHECK_STRNE_FATAL(cfg.sw_images[sw_type], "")
    `DV_CHECK_FATAL(mem inside {Rom, [RamMain0:RamMain15], FlashBank0Data, FlashBank1Data},
        $sformatf("SW symbol cannot appear in %0s mem", mem))

    // Find the symbol in the sw elf file.
    sw_symbol_get_addr_size({cfg.sw_images[sw_type], ".elf"}, symbol, addr, size);
    `DV_CHECK_EQ_FATAL(size, data.size())

    addr_mask = (2**$clog2(cfg.mem_bkdr_util_h[mem].get_size_bytes()))-1;
    mem_addr = addr & addr_mask;
    `uvm_info(`gfn, $sformatf({"Overwriting symbol \"%s\" via backdoor in %0s: ",
                               "abs addr = 0x%0h, mem addr = 0x%0h, size = %0d, ",
                               "addr_mask = 0x%0h"},
                              symbol, mem, addr, mem_addr, size, addr_mask), UVM_LOW)
    for (int i = 0; i < size; i++) mem_bkdr_write8(mem, mem_addr + i, data[i]);

    if (mem == Rom) begin
      `uvm_info(`gfn, "Regenerate ROM digest and update via backdoor", UVM_LOW)
      cfg.mem_bkdr_util_h[mem].update_rom_digest(RndCnstRomCtrlScrKey, RndCnstRomCtrlScrNonce);
    end
  endfunction

  // General-use function to backdoor write a byte of data to any selected memory type
  //
  // TODO: Add support for tiled RAM memories.
  virtual function void mem_bkdr_write8(input chip_mem_e mem,
                                        input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                        input byte data);
    byte prev_data;
    if (mem == Rom) begin
      bit [127:0] key = RndCnstRomCtrlScrKey;
      bit [63:0] nonce = RndCnstRomCtrlScrNonce;
      prev_data = cfg.mem_bkdr_util_h[mem].rom_encrypt_read8(addr, key, nonce);
      cfg.mem_bkdr_util_h[mem].rom_encrypt_write8(addr, data, key, nonce);
    end else begin // flash
      prev_data = cfg.mem_bkdr_util_h[mem].read8(addr);
      cfg.mem_bkdr_util_h[mem].write8(addr, data);
    end
    `uvm_info(`gfn, $sformatf("addr %0h = 0x%0h --> 0x%0h", addr, prev_data, data), UVM_HIGH)
  endfunction

  // LC state transition tasks
  // This function takes the token value from the four LC_CTRL token CSRs, then runs through
  // cshake128 to get a 768-bit XORed token output.
  // The first 128 bits of the decoded token should match the OTP paritition's descrambled tokens
  // value.
  virtual function bit [TokenWidthBit-1:0] dec_otp_token_from_lc_csrs(
      bit [7:0] token_in[TokenWidthByte]);

    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;

    digestpp_dpi_pkg::c_dpi_cshake128(token_in, "", "LC_CTRL", TokenWidthByte,
                                      kmac_pkg::AppDigestW/8, dpi_digest);

    digest_bits = {<< byte {dpi_digest}};
    return (digest_bits[TokenWidthBit-1:0]);
  endfunction


  // LC_CTRL JTAG tasks
  virtual task wait_lc_status(lc_ctrl_status_e expect_status, int max_attemp = 5000);
    int i;
    for (i = 0; i < max_attemp; i++) begin
      bit [TL_DW-1:0] status_val;
      lc_ctrl_status_e dummy;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.status.get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          status_val);

      // Ensure that none of the other status bits are set.
      `DV_CHECK_EQ(status_val >> dummy.num(), 0,
                   $sformatf("Unexpected status error %0h", status_val))
      if (status_val[expect_status]) begin
        `uvm_info(`gfn, $sformatf("LC status %0s.", expect_status.name), UVM_LOW)
        break;
      end
    end

    if (i > max_attemp) begin
      `uvm_fatal(`gfn, $sformatf("max attempt reached to get lc status %0s!", expect_status.name))
    end
  endtask

  virtual task wait_lc_ready(bit allow_err = 1);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = allow_err;
    wait_lc_status(LcReady);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
  endtask

  // Use JTAG interface to transit LC_CTRL from one state to the valid next state.
  // Currently support the following transitions:
  // 1). RAW state -> test unlock state N
  //     This transition will use default raw unlock token.
  // 2). Test lock state N -> test unlock state N+1
  //     This transition requires user to input the correct test unlock token.
  virtual task jtag_lc_state_transition(dec_lc_state_e src_state,
                                        dec_lc_state_e dest_state,
                                        bit [TokenWidthBit-1:0] test_unlock_token = 0);
    bit [TL_DW-1:0] actual_src_state;
    bit valid_transition;
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h,
                                        actual_src_state);
    `DV_CHECK_EQ({DecLcStateNumRep{src_state}}, actual_src_state)

    // Check if the requested transition is valid.
    case (src_state)
      DecLcStRaw: begin
        if (dest_state inside {DecLcStTestUnlocked0, DecLcStTestUnlocked1, DecLcStTestUnlocked2,
                               DecLcStTestUnlocked3, DecLcStTestUnlocked4, DecLcStTestUnlocked5,
                               DecLcStTestUnlocked6, DecLcStTestUnlocked7, DecLcStScrap}) begin
          valid_transition = 1;
          test_unlock_token = RndCnstRawUnlockToken;
        end
      end
      DecLcStTestLocked0: begin
        if (dest_state inside {DecLcStTestUnlocked1, DecLcStTestUnlocked2, DecLcStTestUnlocked3,
                               DecLcStTestUnlocked4, DecLcStTestUnlocked5, DecLcStTestUnlocked6,
                               DecLcStTestUnlocked7, DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
      DecLcStTestLocked1: begin
        if (dest_state inside {DecLcStTestUnlocked2, DecLcStTestUnlocked3, DecLcStTestUnlocked4,
                               DecLcStTestUnlocked5, DecLcStTestUnlocked6,DecLcStTestUnlocked7,
                               DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
      DecLcStTestLocked2: begin
        if (dest_state inside {DecLcStTestUnlocked3, DecLcStTestUnlocked4, DecLcStTestUnlocked5,
                               DecLcStTestUnlocked6, DecLcStTestUnlocked7, DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
      DecLcStTestLocked3: begin
        if (dest_state inside {DecLcStTestUnlocked4, DecLcStTestUnlocked5, DecLcStTestUnlocked6,
                               DecLcStTestUnlocked7, DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
      DecLcStTestLocked4: begin
        if (dest_state inside {DecLcStTestUnlocked5, DecLcStTestUnlocked6, DecLcStTestUnlocked7,
                               DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
      DecLcStTestLocked5: begin
        if (dest_state inside {DecLcStTestUnlocked6, DecLcStTestUnlocked7, DecLcStScrap}) begin
          valid_transition = 1;
        end
      end
       DecLcStTestLocked6: begin
        if (dest_state inside {DecLcStTestUnlocked7, DecLcStScrap}) valid_transition = 1;
      end
     default: `uvm_fatal(`gfn, $sformatf("%0s src state not supported", src_state.name))
    endcase

    if (!valid_transition) begin
      `uvm_fatal(`gfn, $sformatf("invalid state transition request from %0s state to %0s",
                                 src_state.name, dest_state.name))
    end

    `uvm_info(`gfn, $sformatf("Start LC transition request from %0s state to %0s state",
                              src_state.name, dest_state.name), UVM_LOW)
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.claim_transition_if.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         prim_mubi_pkg::MuBi8True);

    // Write LC state transition token.
    begin
      bit [TL_DW-1:0] token_csr_vals[4] = {<< 32 {{>> 8 {test_unlock_token}}}};
      foreach (token_csr_vals[index]) begin
        jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_token[index].get_offset(),
                                             p_sequencer.jtag_sequencer_h,
                                             token_csr_vals[index]);
      end
    end

    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_target.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         {DecLcStateNumRep{dest_state}});
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_cmd.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         1);
    `uvm_info(`gfn, "Sent LC transition request", UVM_LOW)

    wait_lc_status(LcTransitionSuccessful);
    `uvm_info(`gfn, "LC transition request succeed!", UVM_LOW)
  endtask

  // These assertions check if OTP image sets the correct mubi type. However, when loading the raw
  // image, the default value is 0 - which not mubi true or false. We expect this unprogrammed
  // all-zero values to be interpreted as false and relax the assertion below.
  // Detailed discussion in #12428.
  virtual function void otp_raw_img_mubi_assertion_ctrl(bit enable);
    if (enable) begin
      // verilog_lint: waive line-length-exceeds-max
      $asserton(0, "tb.dut.top_earlgrey.u_csrng.u_csrng_core.u_prim_mubi8_sync_sw_app_read.PrimMubi8SyncCheckTransients_A");
      // verilog_lint: waive line-length-exceeds-max
      $asserton(0, "tb.dut.top_earlgrey.u_entropy_src.u_entropy_src_core.u_prim_mubi8_sync_es_fw_over.PrimMubi8SyncCheckTransients_A");
      // verilog_lint: waive line-length-exceeds-max
      $asserton(0, "tb.dut.top_earlgrey.u_entropy_src.u_entropy_src_core.u_prim_mubi8_sync_es_fw_read.PrimMubi8SyncCheckTransients_A");
    end else begin
      // verilog_lint: waive line-length-exceeds-max
      $assertoff(0, "tb.dut.top_earlgrey.u_csrng.u_csrng_core.u_prim_mubi8_sync_sw_app_read.PrimMubi8SyncCheckTransients_A");
      // verilog_lint: waive line-length-exceeds-max
      $assertoff(0, "tb.dut.top_earlgrey.u_entropy_src.u_entropy_src_core.u_prim_mubi8_sync_es_fw_over.PrimMubi8SyncCheckTransients_A");
      // verilog_lint: waive line-length-exceeds-max
      $assertoff(0, "tb.dut.top_earlgrey.u_entropy_src.u_entropy_src_core.u_prim_mubi8_sync_es_fw_read.PrimMubi8SyncCheckTransients_A");
    end
  endfunction

endclass : chip_sw_base_vseq
