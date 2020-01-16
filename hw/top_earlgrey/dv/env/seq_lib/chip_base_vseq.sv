// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_vseq extends dv_base_vseq #(
    .CFG_T               (chip_env_cfg),
    .RAL_T               (chip_reg_block),
    .COV_T               (chip_env_cov),
    .VIRTUAL_SEQUENCER_T (chip_virtual_sequencer)
  );
  `uvm_object_utils(chip_base_vseq)

  // knobs to enable pre_start routines
  bit do_cpu_init = 1'b1; // boot cpu

  // knobs to enable post_start routines

  // various knobs to enable certain routines

  // local state variables
  cpu_test_state_e cpu_test_state;
  uint cpu_test_timeout_ns = 500_000; // 500us

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cpu_test_state = CpuUnderReset;
    if (cfg.stub_cpu) begin
      do_cpu_init = 1'b0;
    end else begin
      // check if this knob is set via plusarg
      void'($value$plusargs("do_cpu_init=%0b", do_cpu_init));
    end
    void'($value$plusargs("cpu_test_timeout_ns=%0d", cpu_test_timeout_ns));
    if (do_cpu_init) cpu_init();
  endtask

  virtual task apply_reset(string kind = "HARD");
    // finish the other resets before system reset. When system reset is done, SW starts to run
    cfg.m_jtag_agent_cfg.do_trst_n();
    super.apply_reset(kind);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.m_uart_agent_cfg.set_baud_rate(BaudRate1Mbps);
    // Initialize gpio pin default states
    cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b1}});
  endtask

  // routine to backdoor load cpu test hex image and bring the cpu out of reset (if required)
  // TODO: for future implementation
  virtual task cpu_init();
    cfg.mem_bkdr_vifs[Rom].load_mem_from_file(cfg.rom_image);
    cfg.mem_bkdr_vifs[FlashBank0].set_mem();
    cfg.mem_bkdr_vifs[FlashBank1].set_mem();

    // TODO: the location of the main execution image should be randomized for either bank in future
    cfg.mem_bkdr_vifs[FlashBank0].load_mem_from_file(cfg.sw_image);
    cpu_test_state = CpuTestRunning;

    // initialize the sw msg monitor
    cfg.sw_msg_monitor_vif.sw_msg_addr = cfg.sw_msg_addr;
    cfg.sw_msg_monitor_vif.add_sw_msg_data_files("rom", cfg.rom_msg_data_file);
    cfg.sw_msg_monitor_vif.add_sw_msg_data_files("sw", cfg.sw_msg_data_file);
    cfg.sw_msg_monitor_vif.ready();
  endtask

  virtual task dut_shutdown();
    // check for pending chip operations and wait for them to complete
    // TODO
  endtask

  virtual task body();
    if (!cfg.stub_cpu) begin
      monitor_cpu_state();
      wait_for_cpu_test_complete(.timeout_ns(cpu_test_timeout_ns));
    end
  endtask : body

  // maintain a specific memory location for cpu test status
  // TODO: using gpio for now - need to use mem loc instead
  // TODO: need to more cpu monitoring logic to separate uvm component
  virtual task monitor_cpu_state();
    fork
      forever begin
        `uvm_info(`gfn, $sformatf("cpu_test_state = %0s", cpu_test_state), UVM_LOW)
        case (cpu_test_state)
          CpuUnderReset: begin
            wait(cpu_test_state == CpuTestRunning);
          end

          CpuTestRunning: begin
            // monitor gpio pins for specific value
            @(cfg.gpio_vif.pins);
            if (cfg.gpio_vif.pins === CpuTestPass) begin
              cpu_test_state = CpuTestPass;
              `uvm_info(`gfn, "cpu test passed!", UVM_LOW)
            end
            else if (cfg.gpio_vif.pins === CpuTestFail) begin
              cpu_test_state = CpuTestFail;
              `uvm_error(`gfn, "cpu test failed!")
            end
          end

          CpuTestPass, CpuTestFail: begin
            wait(cpu_test_state == CpuUnderReset);
          end
        endcase
      end
    join_none
  endtask

  // wait for cpu test to finish
  virtual task wait_for_cpu_test_complete(uint timeout_ns = 500_000);
    fork
      begin: isolation_thread
        fork
          begin: timeout_thread
            #(timeout_ns * 1ns);
            // TODO: uncomment after c framework is in place
            // `uvm_fatal(`gfn, $sformatf("timeout occurred - in cpu test state %0s",
            //                             cpu_test_state.name()))
          end: timeout_thread

          if (cpu_test_state == CpuTestRunning) begin: cpu_state_thread
            wait (cpu_test_state inside {CpuTestPass, CpuTestFail});
          end: cpu_state_thread
        join_any
        disable fork;
      end: isolation_thread
    join
  endtask

 endclass : chip_base_vseq
