// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_power_idle_load_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_power_idle_load_vseq)

  uint timeout_ns = 1;
  int duty_cycle[NUM_PWM_CHANNELS] = '{6,11,27,8,17,7};
  uint pkt_cnt[NUM_PWM_CHANNELS]  = '{default : 0};
  localparam uint CLOCK_PERIOD = 32;

  `uvm_object_new

  virtual task body();
    super.body();

    fork

      begin : GPIO_CHECK
        // Check IOA2 = 0
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "GPIO active",
                 "timeout waiting for SW sync GPIO (1)",
                 cfg.sw_test_timeout_ns)
        `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '0,
                 $sformatf("Timed out waiting for IOA2 == %0h", 0),
                 timeout_ns)
        // Check IOA2 = 1
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "all HW is active",
                 "timeout waiting for SW sync GPIO (2)",
                 cfg.sw_test_timeout_ns)
        `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '1,
                 $sformatf("Timed out waiting for IOA2 == %0h", 1),
                 timeout_ns)
        // Check IOA2 = 0
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "Prepare to exit",
                 "timeout waiting for SW sync GPIO (3)",
                 cfg.sw_test_timeout_ns)
        `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '0,
                 $sformatf("Timed out waiting for IOA2 == %0h", 0),
                 timeout_ns)
      end : GPIO_CHECK

      begin : PWM_CHECK
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "PWM active",
                 "timeout waiting for SW sync PWM (1)",
                 cfg.sw_test_timeout_ns)
        foreach (cfg.m_pwm_monitor_cfg[i]) begin
          cfg.m_pwm_monitor_cfg[i].active = 1;
        end
        fork
          collect_pwm_data();   // this is infinite task
        join_none
        `DV_WAIT(cfg.sw_logger_vif.printed_log == "Prepare to exit",
                 "timeout waiting for SW PWM (2)",
                 cfg.sw_test_timeout_ns)
        foreach (cfg.m_pwm_monitor_cfg[i]) begin
          cfg.m_pwm_monitor_cfg[i].active = 0;
        end
      end : PWM_CHECK

    join

  endtask : body

  virtual task collect_pwm_data();
    pwm_item item[NUM_PWM_CHANNELS];
    foreach(p_sequencer.pwm_rx_fifo[i]) begin
      automatic int j = i;
      fork begin
        forever begin
          process_pwm_data(j);
        end
      end join_none
    end
  endtask : collect_pwm_data

  virtual task process_pwm_data(int channel);
    pwm_item item;

    p_sequencer.pwm_rx_fifo[channel].get(item);
    pkt_cnt[channel]++;

    // During device init, pulse at each channel started with its
    // default value(1) at random time, which creates false
    // duration initially.
    // Flushing first 2 packets will remove such a false alarm.
    if (pkt_cnt[channel] <= 2) return;

    if (item.period != CLOCK_PERIOD) begin
      `uvm_error(`gfn, $sformatf("PWMCH%0d : pkt%0d Clock period is wrong.  rcv : %0d  exp : %0d",
                                 channel, pkt_cnt[channel], item.period, CLOCK_PERIOD))
    end
    if (item.active_cnt != duty_cycle[channel]) begin
      `uvm_error(`gfn, $sformatf("PWMCH%0d : Dutycycle mismatch. invert: %0d  rcv : %0d  exp : %0d",
                                 channel, item.invert, item.active_cnt, duty_cycle[channel]))
    end
  endtask // process_pwm_data

  virtual task post_start();
    super.post_start();
    foreach(p_sequencer.pwm_rx_fifo[i]) begin
      if(pkt_cnt[i] <= 3) begin
        `uvm_error(`gfn, $sformatf("PWMCH%0d : no toggling signal", i))
      end
    end
  endtask : post_start

endclass : chip_sw_power_idle_load_vseq
