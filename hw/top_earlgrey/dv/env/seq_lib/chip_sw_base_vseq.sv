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
    set_and_release_sw_strap_nonblocking();
    // Disable mem checks in scoreboard - it does not factor in memory scrambling.
    cfg.en_scb_mem_chk = 1'b0;
  endtask

  // Drive sw_strap pins only when the ROM / test ROM code is active
  virtual task set_and_release_sw_strap_nonblocking();
    sw_test_status_e prev_status = SwTestStatusUnderReset;
    fork begin
      forever begin
        wait (cfg.sw_test_status_vif.sw_test_status != prev_status);
        case (cfg.sw_test_status_vif.sw_test_status)
          SwTestStatusInBootRom: begin
            cfg.chip_vif.sw_straps_if.drive({3{cfg.use_spi_load_bootstrap}});
          end
          SwTestStatusInTest: begin
            cfg.chip_vif.sw_straps_if.disconnect();
          end
          default: ;
        endcase
        prev_status = cfg.sw_test_status_vif.sw_test_status;
      end
    end join_none
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // Reset the sw_test_status.
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;

    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  // Initialize the chip to enable SW to boot up and execute code.
  //
  // Backdoor load the sw test image, initialize memories, sw logger and test status interfaces.
  // Note that this function is called the moment POR_N asserts. The chip resources including the
  // CPU are brought out of reset much later, after the pwrmgr has gone through the wakeup sequence.
  // Invoke cfg.chip_vif.cpu_clk_rst_vif.wait_for_reset() to bring the simulation to the point where
  // the CPU is out of reset and ready to execute code.
  virtual task cpu_init();
     int size_bytes;
     int total_bytes;

    `uvm_info(`gfn, "Starting cpu_init", UVM_MEDIUM)

    // Initialize the sw logger interface.
    foreach (cfg.sw_images[i]) begin
      if (i inside {SwTypeRom, SwTypeDebug, SwTypeTestSlotA, SwTypeTestSlotB}) begin
        cfg.sw_logger_vif.add_sw_log_db(cfg.sw_images[i]);
      end
    end
    cfg.sw_logger_vif.sw_log_addr = SW_DV_LOG_ADDR;
    cfg.sw_logger_vif.write_sw_logs_to_file = cfg.write_sw_logs_to_file;
    cfg.sw_logger_vif.ready();

    // Initialize the sw test status.
    cfg.sw_test_status_vif.sw_test_status_addr = SW_DV_TEST_STATUS_ADDR;

    `uvm_info(`gfn, "Initializing SRAMs", UVM_MEDIUM)

    // Assume each tile contains the same number of bytes.
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
    // as early portions of ROM will initialize it to the correct value.
    // The randomization here is just to ensure we do not have x's in the memory.
    for (int ram_idx = 0; ram_idx < cfg.num_ram_ret_tiles; ram_idx++) begin
      cfg.mem_bkdr_util_h[chip_mem_e'(RamRet0 + ram_idx)].randomize_mem();
    end

    `uvm_info(`gfn, "Initializing ROM", UVM_MEDIUM)
    // Backdoor load memories with sw images.
`ifdef DISABLE_ROM_INTEGRITY_CHECK
    cfg.mem_bkdr_util_h[Rom].load_mem_from_file({cfg.sw_images[SwTypeRom], ".32.vmem"});
`else
    cfg.mem_bkdr_util_h[Rom].load_mem_from_file({cfg.sw_images[SwTypeRom], ".39.scr.vmem"});
`endif

    if (cfg.sw_images.exists(SwTypeTestSlotA)) begin
      if (cfg.use_spi_load_bootstrap) begin
        `uvm_info(`gfn, "Initializing SPI flash bootstrap", UVM_MEDIUM)
        spi_device_load_bootstrap({cfg.sw_images[SwTypeTestSlotA], ".64.vmem"});
        cfg.use_spi_load_bootstrap = 1'b0;
      end else begin
        cfg.mem_bkdr_util_h[FlashBank0Data].load_mem_from_file(
            {cfg.sw_images[SwTypeTestSlotA], ".64.scr.vmem"});
      end
    end
    if (cfg.sw_images.exists(SwTypeTestSlotB)) begin
      // TODO: support bootstrapping entire flash address space, not just slot A.
      cfg.mem_bkdr_util_h[FlashBank1Data].load_mem_from_file(
          {cfg.sw_images[SwTypeTestSlotB], ".64.scr.vmem"});
    end

    config_jitter();

    `uvm_info(`gfn, "cpu_init completed", UVM_MEDIUM)
  endtask

  // The jitter enable mechanism is different from test_rom and rom right now.
  // That's why below there is both a symbol overwrite and an otp backdoor load.
  // Once test_rom and rom are consistent in this area, the symbol backdoor load
  // can be removed.
  task config_jitter();
    bit en_jitter;
    void'($value$plusargs("en_jitter=%0d", en_jitter));
    if (en_jitter) begin
      // enable for test_rom
      bit [7:0] en_jitter_arr[] = {1};
      sw_symbol_backdoor_overwrite("kJitterEnabled", en_jitter_arr, SwTypeRom);

      // enable for rom
      cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgJitterEnOffset,
                                       prim_mubi_pkg::MuBi4True);
    end else begin
      // rom blindly copies from otp, backdoor load a false value
      cfg.mem_bkdr_util_h[Otp].write32(otp_ctrl_reg_pkg::CreatorSwCfgJitterEnOffset,
                                       prim_mubi_pkg::MuBi4False);
    end
  endtask

  virtual function void main_sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key = RndCnstSramCtrlMainSramKey,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce = RndCnstSramCtrlMainSramNonce,
      bit [38:0] flip_bits = '0);
    _sram_bkdr_write32(addr, data, 1, key, nonce, flip_bits);
  endfunction

  virtual function void ret_sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key = RndCnstSramCtrlRetAonSramKey,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce = RndCnstSramCtrlRetAonSramNonce,
      bit [38:0] flip_bits = '0);
    _sram_bkdr_write32(addr, data, 0, key, nonce, flip_bits);
  endfunction

  // scrambled address may cross the tile, this function will find out what tile the address is
  // located and backdoor write to it.
  protected function void _sram_bkdr_write32(
      bit [bus_params_pkg::BUS_AW-1:0] addr,
      bit [31:0] data,
      bit is_main_ram, // if 1, main ram, otherwise, ret ram
      bit [sram_scrambler_pkg::SRAM_KEY_WIDTH-1:0]   key,
      bit [sram_scrambler_pkg::SRAM_BLOCK_WIDTH-1:0] nonce,
      bit [38:0] flip_bits);

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
    cfg.mem_bkdr_util_h[mem].write39integ(addr_scr & addr_mask, data_scr ^ flip_bits);
  endfunction

  virtual task body();
    cfg.sw_test_status_vif.set_num_iterations(num_trans);
    // Initialize the CPU to kick off the sw test. TODO: Should be called in pre_start() instead.
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
          wait (cfg.sw_test_status_vif.sw_test_done);
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

  // Configure the provided spi_agent_cfg to use flash mode, and add the
  // specification for the following common commands:
  //   ReadSFDP, ReadStatus1, WriteEnable, ChipErase, and PageProgram.
  virtual function void spi_agent_configure_flash_cmds(spi_agent_cfg agent_cfg);
    spi_flash_cmd_info info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashReadSfdp;
    info.num_lanes = 1;
    info.dummy_cycles = 8;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashReadJedec;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashReadSts1;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashReadSts2;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashReadSts3;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashReadNormal;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashReadFast;
    info.num_lanes = 1;
    info.dummy_cycles = 8;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashReadDual;
    info.num_lanes = 2;
    info.dummy_cycles = 8;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashReadQuad;
    info.num_lanes = 4;
    info.dummy_cycles = 8;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashWriteEnable;
    info.num_lanes = 0;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashWriteSts1;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 1;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashWriteSts2;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 1;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashWriteSts3;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 1;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrDisabled;
    info.opcode = SpiFlashChipErase;
    info.num_lanes = 0;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashSectorErase;
    info.num_lanes = 0;
    info.dummy_cycles = 0;
    info.write_command = 0;
    agent_cfg.add_cmd_info(info);

    info = spi_flash_cmd_info::type_id::create("info");
    info.addr_mode = SpiFlashAddrCfg;
    info.opcode = SpiFlashPageProgram;
    info.num_lanes = 1;
    info.dummy_cycles = 0;
    info.write_command = 1;
    agent_cfg.add_cmd_info(info);

    agent_cfg.spi_func_mode = SpiModeFlash;
  endfunction

  // Periodically probe the device for its busy bit and wait for up to
  // `timeout_ns` nanoseconds for it to be de-asserted. Commands sent to the
  // device will be spaced no less than `min_interval_ns` nanoseconds (with a
  // random additional delay). In some cases, using a longer interval can speed
  // up simulation.
  virtual task spi_host_wait_on_busy(
      uint timeout_ns = default_spinwait_timeout_ns,
      uint min_interval_ns = 1000);
    spi_host_flash_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    `DV_SPINWAIT(
      while (1) begin
        cfg.clk_rst_vif.wait_clks($urandom_range(1, 100));
        `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                      opcode == SpiFlashReadSts1;
                                      address_q.size() == 0;
                                      payload_q.size() == 1;
                                      read_size == 1;)
        `uvm_send(m_spi_host_seq)
        // bit 0 is busy bit
        if (m_spi_host_seq.rsp.payload_q[0][0] === 0) break;
        #(min_interval_ns);
      end,
      ,
      timeout_ns
    )
  endtask

  // Performs the write command sequence on the spi_host agent, with
  // a WriteEnable command, followed by the specified command from the
  // `write_command`, then polling for the busy bit to clear.  `busy_timeout_ns`
  // and `busy_poll_interval_ns` work similarly as the parameters for
  // `spi_host_wait_on_busy`.
  virtual task spi_host_flash_issue_write_cmd(
      spi_host_flash_seq write_command,
      uint busy_timeout_ns = default_spinwait_timeout_ns,
      uint busy_poll_interval_ns = 1000);
    spi_host_flash_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    m_spi_host_seq.opcode = SpiFlashWriteEnable;
    `uvm_send(m_spi_host_seq);

    `uvm_send(write_command);

    spi_host_wait_on_busy(busy_timeout_ns, busy_poll_interval_ns);
  endtask

  // Load the flash binary specified by the `sw_image` path by sending a chip
  // erase, then programming pages in sequence via the SPI flash interface
  // presented by the ROM. Afterwards, bring the software straps back to 0,
  // and issue a power-on reset.
  // The `sw_image` path should point to an image usable by the
  // `read_sw_frames` task.
  // This task assumes the device was booted with software straps set before
  // entry. In addition, it expects that the spi_agent was connected to the
  // spi_device and is ready to issue flash transactions.
  virtual task spi_device_load_bootstrap(string sw_image);
    spi_host_flash_seq m_spi_host_seq;
    byte sw_byte_q[$];
    uint bytes_to_write;
    uint byte_cnt = 0;
    uint SPI_FLASH_PAGE_SIZE = 256;

    // Set CSB inactive times to reasonable values. sys_clk is at 24 MHz, and
    // it needs to capture CSB pulses.
    cfg.m_spi_host_agent_cfg.min_idle_ns_after_csb_drop = 50;
    cfg.m_spi_host_agent_cfg.max_idle_ns_after_csb_drop = 200;

    // Configure the spi_agent for flash mode and add command info.
    spi_agent_configure_flash_cmds(cfg.m_spi_host_agent_cfg);

    // Wait for the commands to be ready
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info[spi_device_pkg::CmdInfoReadSfdp].opcode),
      .exp_data(SpiFlashReadSfdp),
      .backdoor(1),
      .spinwait_delay_ns(5000));
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info[spi_device_pkg::CmdInfoReadStatus1].opcode),
      .exp_data(SpiFlashReadSts1),
      .backdoor(1),
      .spinwait_delay_ns(5000));
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info_wren.opcode),
      .exp_data(SpiFlashWriteEnable),
      .backdoor(1),
      .spinwait_delay_ns(5000));

    read_sw_frames(sw_image, sw_byte_q);

    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    m_spi_host_seq.opcode = SpiFlashChipErase;
    spi_host_flash_issue_write_cmd(
      .write_command(m_spi_host_seq),
      .busy_timeout_ns(40_000_000),
      .busy_poll_interval_ns(1_000_000));

    while (sw_byte_q.size > byte_cnt) begin
      `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
      m_spi_host_seq.opcode = SpiFlashPageProgram;
      m_spi_host_seq.address_q = {byte_cnt[23:16], byte_cnt[15:8], byte_cnt[7:0]};
      if (SPI_FLASH_PAGE_SIZE < (sw_byte_q.size() - byte_cnt)) begin
        bytes_to_write = SPI_FLASH_PAGE_SIZE;
      end else begin
        bytes_to_write = sw_byte_q.size() - byte_cnt;
      end
      for (int i = 0; i < bytes_to_write; i++) begin
        m_spi_host_seq.payload_q.push_back(sw_byte_q[byte_cnt + i]);
      end
      spi_host_flash_issue_write_cmd(m_spi_host_seq);
      byte_cnt += bytes_to_write;
    end

    cfg.chip_vif.sw_straps_if.drive(3'h0);
    assert_por_reset();
  endtask

  // Read the flash image pointed to by the `sw_image` path, and place the
  // data into the `sw_byte_q`. The flash image is assumed to consist of
  // contiguous data starting from the base of flash.
  virtual function void read_sw_frames(string sw_image, ref byte sw_byte_q[$]);
    int num_returns;
    int mem_fd = $fopen(sw_image, "r");
    bit [63:0] word_data[4];
    string addr;

    while (!$feof(mem_fd)) begin
      num_returns = $fscanf(mem_fd, "%s %h %h %h %h", addr, word_data[0], word_data[1],
                            word_data[2], word_data[3]);
      if (num_returns <= 1) continue;
      for (int i = 0; i < num_returns - 1; i++) begin
        repeat (8) begin
          sw_byte_q.push_back(word_data[i][7:0]);
          word_data[i] = word_data[i] >> 8;
        end
      end
    end
    $fclose(mem_fd);
  endfunction

  // Backdoor-read or override a const symbol in SW to modify the behavior of the test.
  //
  // In the extended test vseq, override the cpu_init() to add this function call.
  // TODO: bootstrap mode not supported.
  // TODO: Need to deal with scrambling.
  virtual function void sw_symbol_backdoor_access(input string symbol,
                                                  inout bit [7:0] data[],
                                                  input sw_type_e sw_type = SwTypeTestSlotA,
                                                  input bit does_not_exist_ok = 0,
                                                  input bit is_write = 0);

    bit [bus_params_pkg::BUS_AW-1:0] addr, mem_addr;
    chip_mem_e mem;
    uint size;
    uint addr_mask;
    string image;
    bit ret;

    // Elf file name checks.
    `DV_CHECK_FATAL(cfg.sw_images.exists(sw_type))
    `DV_CHECK_STRNE_FATAL(cfg.sw_images[sw_type], "")

    // Find the symbol in the sw elf file.
    image = $sformatf("%0s.elf", cfg.sw_images[sw_type]);
    ret = dv_utils_pkg::sw_symbol_get_addr_size(image, symbol, does_not_exist_ok, addr, size);
    if (!ret) begin
      string msg = $sformatf("Failed to find symbol %0s in %0s", symbol, image);
      if (does_not_exist_ok) begin
        `uvm_info(`gfn, msg, UVM_LOW)
        return;
      end else `uvm_fatal(`gfn, msg)
    end
    `DV_CHECK_EQ_FATAL(size, data.size())

    // Infer mem from address.
    `DV_CHECK(cfg.get_mem_from_addr(addr, mem))
    `DV_CHECK_FATAL(mem inside {Rom, [RamMain0:RamMain15], FlashBank0Data, FlashBank1Data},
        $sformatf("SW symbol %0s is not expected to appear in %0s mem", symbol, mem))

    addr_mask = (2**$clog2(cfg.mem_bkdr_util_h[mem].get_size_bytes()))-1;
    mem_addr = addr & addr_mask;

    if (is_write) begin
      `uvm_info(`gfn, $sformatf({"Overwriting symbol \"%s\" via backdoor in %0s: ",
                               "abs addr = 0x%0h, mem addr = 0x%0h, size = %0d, ",
                               "addr_mask = 0x%0h"},
                              symbol, mem, addr, mem_addr, size, addr_mask), UVM_LOW)
      for (int i = 0; i < size; i++) mem_bkdr_write8(mem, mem_addr + i, data[i]);

      // TODO: Move this specialization to an extended class called rom_bkdr_util.
      if (mem == Rom) begin
        `uvm_info(`gfn, "Regenerate ROM digest and update via backdoor", UVM_LOW)
        cfg.mem_bkdr_util_h[mem].update_rom_digest(RndCnstRomCtrlScrKey, RndCnstRomCtrlScrNonce);
      end
    end else begin
      `uvm_info(`gfn, $sformatf({"Reading symbol \"%s\" via backdoor in %0s: ",
                             "abs addr = 0x%0h, mem addr = 0x%0h, size = %0d, ",
                             "addr_mask = 0x%0h"},
                            symbol, mem, addr, mem_addr, size, addr_mask), UVM_LOW)
      for (int i = 0; i < size; i++) mem_bkdr_read8(mem, mem_addr + i, data[i]);
    end
  endfunction

  // Backdoor-read a const symbol in SW to make decisions based on SW constants.
  //
  // Wrapper function for reads via sw_symbol_backdoor_access.
  virtual function void sw_symbol_backdoor_read(input string symbol,
                                                inout bit [7:0] data[],
                                                input sw_type_e sw_type = SwTypeTestSlotA,
                                                input bit does_not_exist_ok = 0);

    sw_symbol_backdoor_access(symbol, data, sw_type, does_not_exist_ok, 0);
    `uvm_info(`gfn, $sformatf("sw_symbol_backdoor_read gets %p", data), UVM_MEDIUM)
  endfunction

  // Backdoor-override a const symbol in SW to modify the behavior of the test.
  //
  // Wrapper function for writes via sw_symbol_backdoor_access.
  virtual function void sw_symbol_backdoor_overwrite(input string symbol,
                                                     input bit [7:0] data[],
                                                     input sw_type_e sw_type = SwTypeTestSlotA,
                                                     input bit does_not_exist_ok = 0);

    sw_symbol_backdoor_access(symbol, data, sw_type, does_not_exist_ok, 1);
  endfunction

  // General-use function to backdoor write a byte of data to any selected memory type
  //
  // TODO: Add support for tiled RAM memories.
  virtual function void mem_bkdr_write8(input chip_mem_e mem,
                                        input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                        input byte data);
    byte prev_data;
    // TODO: Move these specializations to extended classes so that no special handling is needed at
    // the call site.
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

  // General-use function to backdoor read a byte of data from any selected memory type
  //
  // TODO: Add support for tiled RAM memories.
  virtual function void mem_bkdr_read8(input chip_mem_e mem,
                                       input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                       output byte data);
    // TODO: Move these specializations to extended classes so that no special handling is needed at
    // the call site.
    if (mem == Rom) begin
      bit [127:0] key = RndCnstRomCtrlScrKey;
      bit [63:0] nonce = RndCnstRomCtrlScrNonce;
      data = cfg.mem_bkdr_util_h[mem].rom_encrypt_read8(addr, key, nonce);
    end else begin // flash
      data = cfg.mem_bkdr_util_h[mem].read8(addr);
    end
    `uvm_info(`gfn, $sformatf("addr %0h = 0x%0h", addr, data), UVM_HIGH)
  endfunction


  // LC state transition tasks
  // This function takes the token value from the four LC_CTRL token CSRs, then runs through
  // cshake128 to get a 768-bit XORed token output.
  // The first 128 bits of the decoded token should match the OTP partition's descrambled tokens
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
  virtual task wait_lc_status(lc_ctrl_status_e expect_status, int max_attempt = 5000);
    int i;
    for (i = 0; i < max_attempt; i++) begin
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

    if (i >= max_attempt) begin
      `uvm_fatal(`gfn, $sformatf("max attempt reached to get lc status %0s!", expect_status.name))
    end
  endtask

  virtual task wait_lc_initialized(bit allow_err = 1, int max_attempt = 5000);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = allow_err;
    wait_lc_status(LcInitialized, max_attempt);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
  endtask

  virtual task wait_lc_ready(bit allow_err = 1, int max_attempt = 5000);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = allow_err;
    wait_lc_status(LcReady, max_attempt);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
  endtask

  virtual task wait_lc_transition_successful(bit allow_err = 1, int max_attempt = 5000);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = allow_err;
    wait_lc_status(LcTransitionSuccessful, max_attempt);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;
  endtask

  // Use JTAG interface to transit LC_CTRL from RAW to TEST_UNLOCKED* states
  // using the VOLATILE_RAW_UNLOCK mode of operation.
  virtual task jtag_lc_state_volatile_raw_unlock(chip_jtag_tap_e target_strap);
    bit [TL_DW-1:0] current_lc_state;
    bit [TL_DW-1:0] transition_ctrl;
    int max_attempt = 5_000;
    dec_lc_state_e dest_state = DecLcStTestUnlocked0;

    wait_lc_ready();
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h,
                                        current_lc_state);
    `DV_CHECK_EQ(DecLcStRaw, current_lc_state)

    `uvm_info(`gfn, $sformatf("Start LC transition request to %0s state", dest_state.name),
                              UVM_LOW)
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.claim_transition_if.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         prim_mubi_pkg::MuBi8True);

    `uvm_info(`gfn, "Switching to VOLATILE_RAW_UNLOCK via JTAG...", UVM_LOW)
    jtag_riscv_agent_pkg::jtag_write_csr(
      ral.lc_ctrl.transition_ctrl.get_offset(),
      p_sequencer.jtag_sequencer_h,
      2);

    jtag_riscv_agent_pkg::jtag_read_csr(
      ral.lc_ctrl.transition_ctrl.get_offset(),
      p_sequencer.jtag_sequencer_h,
      transition_ctrl);
    `DV_CHECK_FATAL(transition_ctrl & (1 << 1), {"VOLATILE_RAW_UNLOCK is not supported by this ",
                    "top level. Check the SecVolatileRawUnlockEn parameter configuration."})

    begin
      bit [TL_DW-1:0] token_csr_vals[4] = {<< 32 {{>> 8 {RndCnstRawUnlockTokenHashed}}}};
      foreach (token_csr_vals[index]) begin
        jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_token[index].get_offset(),
                                             p_sequencer.jtag_sequencer_h,
                                             token_csr_vals[index]);
      end
    end

    // Switch strap configuration before requesting volatile raw unlock. This is to
    // switch to rv_dm in test_unlocked0.
    cfg.chip_vif.tap_straps_if.drive(target_strap);

    `uvm_info(`gfn, "Sent LC transition request", UVM_LOW)
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_target.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         {DecLcStateNumRep{DecLcStTestUnlocked0}});
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.transition_cmd.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         1);

    if (target_strap == JtagTapLc) begin
      wait_lc_transition_successful(.max_attempt(max_attempt));
      jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.claim_transition_if.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         prim_mubi_pkg::MuBi8False);
    end else begin
      cfg.clk_rst_vif.wait_clks($urandom_range(10000, 20000));
    end
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
    int max_attempt;

    // Check that the LC controller is ready to accept a transition.
    wait_lc_ready();

    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h,
                                        actual_src_state);
    `DV_CHECK_EQ({DecLcStateNumRep{src_state}}, actual_src_state)

    // Check if the requested transition is valid.
    case (src_state)
      DecLcStRaw: begin
        if (dest_state inside {DecLcStTestUnlocked0, DecLcStTestUnlocked1, DecLcStTestUnlocked2,
                               DecLcStTestUnlocked3, DecLcStTestUnlocked4, DecLcStTestUnlocked5,
                               DecLcStTestUnlocked6, DecLcStTestUnlocked7}) begin
          valid_transition = 1;
          test_unlock_token = RndCnstRawUnlockToken;
        end else if (dest_state == DecLcStScrap) begin
          // This transition is unconditional and can use test_unlock_token = 0.
          valid_transition = 1;
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
      DecLcStTestUnlocked0,
      DecLcStTestUnlocked1,
      DecLcStTestUnlocked2,
      DecLcStTestUnlocked3,
      DecLcStTestUnlocked4,
      DecLcStTestUnlocked5,
      DecLcStTestUnlocked6,
      DecLcStTestUnlocked7: begin
        if (dest_state inside {DecLcStProd, DecLcStScrap}) valid_transition = 1;
      end
      DecLcStDev,
      DecLcStProd: begin
        if(dest_state inside {DecLcStRma, DecLcStScrap}) valid_transition = 1;
      end
      DecLcStProdEnd,
      DecLcStRma: begin
        if(dest_state inside {DecLcStScrap}) valid_transition = 1;
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

    // Transitions into RMA take much longer, hence we increase this number.
    if (dest_state == DecLcStRma) begin
      max_attempt = 50_000;
    end else begin
      max_attempt = 5_000;
    end
    wait_lc_transition_successful(.max_attempt(max_attempt));
    `uvm_info(`gfn, "LC transition request succeeded successfully!", UVM_LOW)
  endtask

  // Acquire the LC_CTRL transition interface mutex by LC JTAG
  protected task claim_transition_interface();
    `uvm_info(`gfn, "Claiming LC controller transition interface by JTAG...", UVM_MEDIUM)
    jtag_riscv_agent_pkg::jtag_write_csr(
        ral.lc_ctrl.claim_transition_if.get_offset(),
        p_sequencer.jtag_sequencer_h,
        prim_mubi_pkg::MuBi8True);
  endtask : claim_transition_interface

  // Bypass IO clock with the external clock
  // using LC_CTRL.CTRL_TRANSITION.EXT_CLOCK_EN
  task switch_to_external_clock();
    // activate the external source clock with 48MHz
    `uvm_info(`gfn, "Setting external clock to 48MHz...", UVM_MEDIUM)
    cfg.chip_vif.ext_clk_if.set_freq_mhz(48);
    cfg.chip_vif.ext_clk_if.set_active(.drive_clk_val(1), .drive_rst_n_val(0));

    // switch OTP to use external clock instead of internal clock
    // wait for LC to be ready, acquire the transition interface mutex and
    // enable external clock
    wait_lc_ready();
    claim_transition_interface();

    // switch to external clock via LC controller
    `uvm_info(`gfn, "Switching to external clock via JTAG...", UVM_MEDIUM)
    jtag_riscv_agent_pkg::jtag_write_csr(
      ral.lc_ctrl.transition_ctrl.get_offset(),
      p_sequencer.jtag_sequencer_h,
      1);
  endtask : switch_to_external_clock

  // Use JTAG interface to program OTP fields.
  virtual task jtag_otp_program32(int addr,
                                  bit [31:0] data);

    bit [TL_DW-1:0] status;
    bit [TL_DW-1:0] err_mask = 0;
    bit idle = 0;
    int base_addr = top_earlgrey_pkg::TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR;
    jtag_riscv_agent_pkg::jtag_write_csr(base_addr +
                                         ral.otp_ctrl_core.direct_access_address.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         addr);

    jtag_riscv_agent_pkg::jtag_write_csr(base_addr +
                                         ral.otp_ctrl_core.direct_access_wdata[0].get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         data[31:0]);

    jtag_riscv_agent_pkg::jtag_write_csr(base_addr +
                                         ral.otp_ctrl_core.direct_access_cmd.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         1 << ral.otp_ctrl_core.direct_access_cmd.wr.get_lsb_pos());


    while (!idle) begin
      jtag_riscv_agent_pkg::jtag_read_csr(base_addr +
                                          ral.otp_ctrl_core.status.get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          status);

      idle = dv_base_reg_pkg::get_field_val(ral.otp_ctrl_core.status.dai_idle, status);

      err_mask = ~((1 << ral.otp_ctrl_core.status.dai_idle.get_lsb_pos()) |
                   (1 << ral.otp_ctrl_core.status.check_pending.get_lsb_pos()));

      `uvm_info(`gfn, $sformatf("Waiting for DAI to become idle = 1, actual: %d!", idle),
         UVM_MEDIUM)

      // If any bits other than dai_idle and check pending are set, error back.
      `DV_CHECK((status & err_mask) == '0, "Otp program failed")
    end
  endtask : jtag_otp_program32

  // End the test with status.
  //
  // SW test code finishes the test sequence usually by returing true or false
  // in the `test_main()` function. However, some tests may need vseq to
  // finish the tests. For example, `chip_sw_sleep_pin_mio_dio_val` checks the
  // PADs output value then finishes the test without waking up the SW again.
  //
  // If pass is 1, then `sw_test_status` is set to SwTestStatusPassed.
  virtual function void override_test_status_and_finish(bit passed);
    cfg.sw_test_status_vif.sw_test_status = (passed) ? SwTestStatusPassed
                                                     : SwTestStatusFailed;
    cfg.sw_test_status_vif.sw_test_done   = 1'b 1;
  endfunction : override_test_status_and_finish

  task assert_por_reset_deep_sleep (int delay = 0);
    repeat (delay) @cfg.chip_vif.pwrmgr_low_power_if.cb;
    cfg.chip_vif.por_n_if.drive(0);
    repeat (6) @cfg.chip_vif.pwrmgr_low_power_if.cb;

    cfg.clk_rst_vif.wait_clks(10);
    cfg.chip_vif.por_n_if.drive(1);
  endtask // assert_por_reset_deep_sleep

  // push button 50us;
  // this task requires proper sysrst_ctrl config
  // see sw/device/tests/pwrmgr_b2b_sleep_reset_test.c
  // 'static void prgm_push_button_wakeup()' for example
  task push_button();
    cfg.chip_vif.pwrb_in_if.drive(0);
    #50us;
    cfg.chip_vif.pwrb_in_if.drive(1);
  endtask // push_button

endclass : chip_sw_base_vseq
