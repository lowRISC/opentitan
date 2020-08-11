// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_base_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_sw_base_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // Reset the sw_test_status.
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  // Backdoor load the sw test image, setup UART, logger and test status interfaces.
  virtual task cpu_init();
    // TODO: Fixing this for now - need to find a way to pass this on to the SW test.
    cfg.m_uart_agent_cfg.set_parity(1'b0, 1'b0);
    cfg.m_uart_agent_cfg.set_baud_rate(cfg.uart_baud_rate);

    // initialize the sw logger interface
    foreach (cfg.sw_types[i]) begin
      cfg.sw_logger_vif.set_sw_name(cfg.sw_types[i]);
    end
    cfg.sw_logger_vif.sw_log_addr = SW_DV_LOG_ADDR;
    cfg.sw_logger_vif.write_sw_logs_to_file = cfg.write_sw_logs_to_file;
    cfg.sw_logger_vif.ready();

    // initialize the sw test status
    cfg.sw_test_status_vif.sw_test_status_addr = SW_DV_TEST_STATUS_ADDR;

    // Initialize the RAM to 0s and flash to all 1s.
    if (cfg.initialize_ram) cfg.mem_bkdr_vifs[Ram].clear_mem();
    cfg.mem_bkdr_vifs[FlashBank0].set_mem();
    cfg.mem_bkdr_vifs[FlashBank1].set_mem();

    // Backdoor load memories with sw images.
    cfg.mem_bkdr_vifs[Rom].load_mem_from_file(cfg.sw_images["rom"]);
    // TODO: the location of the main execution image should be randomized for either bank in future
    cfg.mem_bkdr_vifs[FlashBank0].load_mem_from_file(cfg.sw_images["sw"]);
    cfg.sw_test_status_vif.sw_test_status = SwTestStatusBooted;
  endtask

  virtual task body();
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
      begin : isolation_thread
        fork
          wait(cfg.sw_test_status_vif.sw_test_done);
          #(cfg.sw_test_timeout_ns * 1ns);
        join_any
        disable fork;
        log_sw_test_status();
      end : isolation_thread
    join
  endtask

  // Print pass / fail message to the log.
  virtual function void log_sw_test_status();
    case (cfg.sw_test_status_vif.sw_test_status)
      SwTestStatusPassed: `uvm_info(`gfn, "SW TEST PASSED!", UVM_LOW)
      SwTestStatusFailed: `uvm_error(`gfn, "SW TEST FAILED!")
      default: begin
        // If the SW test has not reached the passed / failed state, then it timed out.
        `uvm_error(`gfn,
                   $sformatf("SW TEST TIMED OUT. STATE: %0s, TIMEOUT = %0d ns\n",
                             cfg.sw_test_status_vif.sw_test_status.name(), cfg.sw_test_timeout_ns))
      end
    endcase
  endfunction

endclass : chip_sw_base_vseq
