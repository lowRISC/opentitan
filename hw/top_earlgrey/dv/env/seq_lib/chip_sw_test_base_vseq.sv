// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_test_base_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_sw_test_base_vseq)

  bit sw_test_done;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // Reset the sw_test_status.
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  // Backdoor load the sw test image, setup UART, logger and test status interfaces.
  virtual task cpu_init();
    // Set 'default' UART baud rate of 2Mbps - this is also programmed by the C test.
    // TODO: Fixing this for now - need to find a way to pass this on to the SW test.
    cfg.m_uart_agent_cfg.set_parity(1'b0, 1'b0);
    cfg.m_uart_agent_cfg.set_baud_rate(BaudRate2Mbps);

    // initialize the sw msg monitor
    foreach (cfg.sw_types[i]) begin
      cfg.sw_logger_vif[cfg.sw_types[i]].sw_log_addr = SW_DV_LOG_ADDR;
      cfg.sw_logger_vif[cfg.sw_types[i]].set_sw_name(cfg.sw_types[i]);
      cfg.sw_logger_vif[cfg.sw_types[i]].ready();
    end

    // initialize the sw test status
    cfg.sw_test_status_vif.sw_test_status_addr = SW_DV_TEST_STATUS_ADDR;

    // Backdoor load memories.
    cfg.mem_bkdr_vifs[Rom].load_mem_from_file(cfg.sw_images["rom"]);
    cfg.mem_bkdr_vifs[FlashBank0].set_mem();
    cfg.mem_bkdr_vifs[FlashBank1].set_mem();
    // TODO: the location of the main execution image should be randomized for either bank in future
    cfg.mem_bkdr_vifs[FlashBank0].load_mem_from_file(cfg.sw_images["sw"]);
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusBooted;
  endtask

  virtual task pre_start();
    super.pre_start();
    cpu_init();
  endtask

  virtual task body();
    // Spawn off a thread to monitor the SW test status.
    fork monitor_sw_test_status(); join_none
  endtask

  // Monitors the SW test status.
  virtual task monitor_sw_test_status();
    `uvm_info(`gfn, "Monitoring the SW test status", UVM_MEDIUM)
    fork
      begin: isolation_thread
        fork
          wait(cfg.sw_test_status_vif.sw_test_done);
          #(cfg.sw_test_timeout_ns * 1ns);
        join_any
        disable fork;
        sw_test_done = 1'b1;
        log_sw_test_status();
      end: isolation_thread
    join
  endtask

  virtual task post_start();
    // Wait for sw test to finish before exiting.
    wait(sw_test_done);
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

endclass : chip_sw_test_base_vseq
