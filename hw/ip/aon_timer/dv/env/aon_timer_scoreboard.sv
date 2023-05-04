// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_scoreboard extends cip_base_scoreboard #(
    .CFG_T(aon_timer_env_cfg),
    .RAL_T(aon_timer_reg_block),
    .COV_T(aon_timer_env_cov)
  );
  `uvm_component_utils(aon_timer_scoreboard)

  // local variables
  local bit  wkup_en;
  local bit  wkup_num_update_due;
  local uint wkup_count;
  local uint prescaler;
  local uint wkup_thold;

  local bit  wdog_en;
  local bit  wdog_regwen;
  local bit  wdog_pause_in_sleep;
  local bit  wdog_num_update_due;
  local uint wdog_count;
  local uint bark_thold;
  local uint bite_thold;

  local bit  wkup_cause;
  local uint wkup_num;
  local uint wdog_bark_num;
  local uint wdog_bite_num;

  // expected values
  local bit intr_status_exp [2];
  local bit wdog_rst_req_exp = 0;

  typedef enum logic {
    WKUP = 1'b0,
    WDOG = 1'b1
  } timers_e;

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      compute_num_clks();
      check_interrupt();
      monitor_interrupts();
    join_none
  endtask

  task monitor_interrupts();
    forever begin
      @(cfg.aon_intr_vif.pins);
      // Sample interrupt pin coverage for interrupt pins
      if (cfg.en_cov) begin
        foreach (cfg.aon_intr_vif.pins[i]) begin
          cov.intr_pins_cg.sample(i, cfg.aon_intr_vif.sample_pin(.idx(i)));
        end
      end
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      if (cfg.en_cov) begin
        //Sample configuration coverage
        cov.timer_cfg_cg.sample(prescaler, bark_thold, bite_thold,
                                wkup_thold, wdog_regwen, wdog_pause_in_sleep, wkup_cause);
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        do_read_check = 1'b0;
        if (data_phase_write) begin
          uint intr_state_val = item.a_data;
          if (intr_state_val[WKUP]) intr_status_exp[WKUP] = 1'b0;
          if (intr_state_val[WDOG]) intr_status_exp[WDOG] = 1'b0;
        end
        // INTR_EN register does not exists in AON timer because the interrupts are
        // enabled as long as timers are enabled.
        if (cfg.en_cov && data_phase_read) begin
          cov.intr_cg.sample(WKUP, wkup_en, item.d_data);
          cov.intr_cg.sample(WDOG, wdog_en, item.d_data);
        end
      end
      "wkup_ctrl": begin
        prescaler = get_reg_fld_mirror_value(ral, csr.get_name(), "prescaler");
        wkup_en   = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
        if (data_phase_write) wkup_num_update_due = 1;
      end
      "wkup_cause": begin
        wkup_cause = csr.get_mirrored_value();
        intr_status_exp[WKUP] = item.a_data;
      end
      "wkup_count": begin
        wkup_count =  csr.get_mirrored_value();
        if (data_phase_write) wkup_num_update_due = 1;
      end
      "wkup_thold": begin
        wkup_thold =  csr.get_mirrored_value();
        if (data_phase_write) wkup_num_update_due = 1;
      end
      "wdog_ctrl": begin
        wdog_en = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
        wdog_pause_in_sleep = get_reg_fld_mirror_value(ral, csr.get_name(), "pause_in_sleep");
      end
      "wdog_count": begin
        wdog_count =  csr.get_mirrored_value();
        if (data_phase_write) wdog_num_update_due = 1;
      end
      "wdog_regwen": begin
        wdog_regwen =  csr.get_mirrored_value();
      end
      "wdog_bark_thold": begin
        bark_thold =  csr.get_mirrored_value();
        if (data_phase_write) wdog_num_update_due = 1;
      end
      "wdog_bite_thold": begin
        bite_thold =  csr.get_mirrored_value();
        if (data_phase_write) wdog_num_update_due = 1;
      end
      "intr_test": begin
        uint intr_test_val = item.a_data;
        if (intr_test_val[WKUP]) intr_status_exp[WKUP] = 1'b1;
        if (intr_test_val[WDOG]) intr_status_exp[WDOG] = 1'b1;
        if (cfg.en_cov) begin
          cov.intr_test_cg.sample(WKUP, intr_test_val[WKUP],
                                  wkup_en, intr_status_exp[WKUP]);
          cov.intr_test_cg.sample(WDOG, intr_test_val[WDOG],
                                  wdog_en, intr_status_exp[WDOG]);
        end
      end
      default: begin
          // No other special behaviour for writes
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

  // Task : check_interrupt
  // wait for expected # of clocks and check for interrupt state reg and pin
  virtual task check_interrupt();
    forever begin
      wait (!under_reset);

      fork : isolation_fork
        fork
          wait (under_reset);
          run_wkup_timer();
          run_wdog_bark_timer();
          run_wdog_bite_timer();
        join_any

        // run_wkup_timer and run_wdog_timer never return so if we've got here then we've gone into
        // reset. Kill the two timer processes then go around and wait until we come out of reset
        // again.
        disable fork;
      join
    end
  endtask : check_interrupt

  virtual task compute_num_clks();
    forever begin : compute_num_clks
      // calculate number of clocks required to have interrupt from wkup
      @(wkup_num_update_due or wdog_num_update_due);
      wait(!under_reset);
      if (wkup_num_update_due) begin
        if (wkup_count <= wkup_thold) begin
          wkup_num = ((wkup_thold - wkup_count + 1) * (prescaler + 1));
        end
        else begin
          wkup_num = 0;
        end
        `uvm_info(`gfn, $sformatf("Calculated WKUP_NUM: %d", wkup_num), UVM_HIGH)
      end
      if (wdog_num_update_due) begin
        // calculate wdog bark
        if (wdog_count < bark_thold) begin
          wdog_bark_num = bark_thold - wdog_count;
        end
        else begin
          wdog_bark_num = 0;
        end
        `uvm_info(`gfn, $sformatf("Calculated wdog_bark_num: %d", wdog_bark_num), UVM_HIGH)
        if (wdog_count < bite_thold) begin
          wdog_bite_num = bite_thold - wdog_count;
        end
        else begin
          wdog_bite_num = 0;
        end
        `uvm_info(`gfn, $sformatf("Calculated wdog_bite_num: %d", wdog_bite_num), UVM_HIGH)
      end
      wkup_num_update_due = 0;
      wdog_num_update_due = 0;
    end // compute_num_clks
  endtask

  virtual task run_wkup_timer();
    forever begin
      wait (wkup_en);
      fork
        begin
          // trying to count how many cycles we need to count
          uint count = 0;
          // It takes 4 aon clks from the write enabling the watchdog to take effect due to the CDC
          // logic.
          cfg.aon_clk_rst_vif.wait_clks(4);
          while (count < wkup_num) begin
            cfg.aon_clk_rst_vif.wait_clks(1);
            // reset the cycle counter when we update the cycle count needed
            count = wkup_num_update_due ? 0 : (count + 1);
            `uvm_info(`gfn, $sformatf("WKUP Timer count: %d", count), UVM_HIGH)
          end
          `uvm_info(`gfn, $sformatf("WKUP Timer expired check for interrupts"), UVM_HIGH)
          intr_status_exp[WKUP] = 1'b1;
          // Interrupt should happen N+1 clock ticks after count == wkup_num.
          cfg.aon_clk_rst_vif.wait_clks(prescaler+1);
          // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
          // to become visible on the top-level pins.
          cfg.clk_rst_vif.wait_clks(5);
          // Check interrupt pin
          `DV_CHECK_CASE_EQ(intr_status_exp[WKUP],
                            cfg.intr_vif.sample_pin(.idx(WKUP)))
          // Check wakeup pin
          `DV_CHECK_CASE_EQ(1,
                            cfg.aon_intr_vif.sample_pin(.idx(1)))
          `uvm_info(`gfn, $sformatf("WKUP Timer check passed."), UVM_HIGH)
        end
        begin
          wait (!wkup_en || !cfg.aon_clk_rst_vif.rst_n);
          `uvm_info(`gfn, $sformatf("WKUP Timer disabled, quit scoring"), UVM_HIGH)
          wkup_en = 0;
        end
      join_any
      disable fork;
    end
  endtask

  virtual task run_wdog_bark_timer();
    forever begin
      wait (wdog_en);
      fork
        begin
          // trying to count how many cycles we need to count
          uint count = 0;
          // It takes 4 aon clks from the write enabling the watchdog to take effect due to the CDC
          // logic.
          cfg.aon_clk_rst_vif.wait_clks(4);
          while (count < wdog_bark_num) begin
            cfg.aon_clk_rst_vif.wait_clks(1);
            // reset the cycle counter when we update the cycle count needed
            count = wdog_num_update_due ? 0 : (count + 1);
            `uvm_info(`gfn, $sformatf("WDOG Bark Timer count: %d", count), UVM_HIGH)
          end
          `uvm_info(`gfn, $sformatf("WDOG Bark Timer expired check for interrupts"), UVM_HIGH)
          intr_status_exp[WDOG] = 1'b1;
          // Propagation delay of one cycle from aon_core to interrupt pins.
          cfg.aon_clk_rst_vif.wait_clks(1);
          // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
          // to become visible on the top-level pins.
          cfg.clk_rst_vif.wait_clks(5);
          // Check interrupt and reset_req pins
          `DV_CHECK_CASE_EQ(intr_status_exp[WDOG],
                            cfg.intr_vif.sample_pin(.idx(WDOG)))

          // Check wakeup pin
          `DV_CHECK_CASE_EQ(intr_status_exp[WDOG],
                            cfg.aon_intr_vif.sample_pin(.idx(1)))
          `uvm_info(`gfn,
                    $sformatf("WDOG INTR Bark: %d",
                              intr_status_exp[WDOG]),
                    UVM_HIGH)
        end
        begin
          wait (!wdog_en || !cfg.aon_clk_rst_vif.rst_n);
          `uvm_info(`gfn, $sformatf("WDOG Timer disabled, quit scoring"), UVM_HIGH)
          wdog_en = 0;
        end
      join_any
      disable fork;
    end
  endtask

  virtual task run_wdog_bite_timer();
    forever begin
      wait (wdog_en);
      fork
        begin
          // trying to count how many cycles we need to count
          uint count = 0;
          // It takes 4 aon clks from the write enabling the watchdog to take effect due to the CDC
          // logic.
          cfg.aon_clk_rst_vif.wait_clks(4);
          while (count < wdog_bite_num) begin
            cfg.aon_clk_rst_vif.wait_clks(1);
            // reset the cycle counter when we update the cycle count needed
            count = wdog_num_update_due ? 0 : (count + 1);
            `uvm_info(`gfn, $sformatf("WDOG Bite Timer count: %d", count), UVM_HIGH)
          end
          `uvm_info(`gfn, $sformatf("WDOG Bite Timer expired check for interrupts"), UVM_HIGH)
          wdog_rst_req_exp = 1'b1;
          // Propagation delay of one cycle from aon_core to interrupt pins.
          cfg.aon_clk_rst_vif.wait_clks(1);
          // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
          // to become visible on the top-level pins.
          cfg.clk_rst_vif.wait_clks(5);
          // Check reset_req pin
          `DV_CHECK_CASE_EQ(wdog_rst_req_exp,
                            cfg.aon_intr_vif.sample_pin(.idx(0)))

          `uvm_info(`gfn,
                    $sformatf("WDOG INTR Bite: %d",
                              wdog_rst_req_exp),
                    UVM_HIGH)
        end
        begin
          wait (!wdog_en || !cfg.aon_clk_rst_vif.rst_n);
          `uvm_info(`gfn, $sformatf("WDOG Timer disabled, quit scoring"), UVM_HIGH)
          wdog_en = 0;
        end
      join_any
      disable fork;
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
