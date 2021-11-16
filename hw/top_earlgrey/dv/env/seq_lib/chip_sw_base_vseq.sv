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

  virtual task dut_init(string reset_kind = "HARD");
    // Reset the sw_test_status.
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  // Backdoor load the sw test image, setup UART, logger and test status interfaces.
  virtual task cpu_init();
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
    // Initialize the RAM to 0s and flash to all 1s.
    if (cfg.initialize_ram) begin
      for (int i = 0; i < cfg.num_ram_main_tiles; i++) begin
        chip_mem_e mem = chip_mem_e'(RamMain0 + i);
        cfg.mem_bkdr_util_h[mem].clear_mem();
      end
    end
    cfg.mem_bkdr_util_h[FlashBank0Data].set_mem();
    cfg.mem_bkdr_util_h[FlashBank1Data].set_mem();

    `uvm_info(`gfn, "Initializing ROM", UVM_MEDIUM)
    // Backdoor load memories with sw images.
    cfg.mem_bkdr_util_h[Rom].load_mem_from_file({cfg.sw_images[SwTypeRom], ".scr.39.vmem"});

    // TODO: the location of the main execution image should be randomized to either bank in future.
    `uvm_info(`gfn, "Initializing flash", UVM_MEDIUM)
    if (cfg.use_spi_load_bootstrap) begin
      spi_device_load_bootstrap({cfg.sw_images[SwTypeTest], ".frames.vmem"});
    end else begin
      cfg.mem_bkdr_util_h[FlashBank0Data].load_mem_from_file(
          {cfg.sw_images[SwTypeTest], ".64.scr.vmem"});
    end
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusBooted;

    `uvm_info(`gfn, "cpu_init done", UVM_MEDIUM)
    // If we load the mem with a file in the same timestamp as we are overwriting a symbol in the
    // ELF file, then adding zero delay helps with avoiding a race condition. Do all symbol
    // overrides after this zero delay.
    #0;
  endtask

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
      `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                     data.size() == SPI_FRAME_BYTE_SIZE;
                                     foreach (data[i]) {data[i] == sw_byte_q[byte_cnt+i];})
      `uvm_send(m_spi_host_seq)
      if (byte_cnt == 0) begin
        // SW erase flash after receiving 1st frame
        wait(cfg.sw_logger_vif.printed_log == "Flash erase successful");
        // sdo for next frame shouldn't be unknown
        cfg.m_spi_agent_cfg.en_monitor_checks = 1;
      end

      cfg.clk_rst_vif.wait_clks(30_000);
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

    // Elf file name checks.
    `DV_CHECK_FATAL(cfg.sw_images.exists(sw_type))
    `DV_CHECK_STRNE_FATAL(cfg.sw_images[sw_type], "")
    `DV_CHECK_FATAL(mem inside {Rom, [RamMain0:RamMain15], FlashBank0Data, FlashBank1Data},
        $sformatf("SW symbol cannot appear in %0s mem", mem))

    // Find the symbol in the sw elf file.
    sw_symbol_get_addr_size({cfg.sw_images[sw_type], ".elf"}, symbol, addr, size);
    `DV_CHECK_EQ_FATAL(size, data.size())
    mem_addr = addr & (cfg.mem_bkdr_util_h[mem].get_size_bytes() - 1);
    `uvm_info(`gfn, $sformatf({"Overwriting symbol \"%s\" via backdoor in %0s: ",
                               "abs addr = 0x%0h, mem addr = 0x%0h, size = %0d"},
                              symbol, mem, addr, mem_addr, size), UVM_MEDIUM)
    for (int i = 0; i < size; i++) mem_bkdr_write8(mem, mem_addr + i, data[i]);
  endfunction

  // General-use function to backdoor write a byte of data to any selected memory type
  //
  // TODO: Add support for tiled RAM memories.
  virtual function void mem_bkdr_write8(input chip_mem_e mem,
                                        input bit [bus_params_pkg::BUS_AW-1:0] addr,
                                        input byte data);
    byte prev_data = cfg.mem_bkdr_util_h[mem].read8(addr);
    cfg.mem_bkdr_util_h[mem].write8(addr, data);
    `uvm_info(`gfn, $sformatf("addr %0h = 0x%0h --> 0x%0h", addr, prev_data, data), UVM_HIGH)
  endfunction

endclass : chip_sw_base_vseq
