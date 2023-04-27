// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwm_pulses_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwm_pulses_vseq)

  `uvm_object_new

  // Dutycycle parameters
  // This should match with parameters in 'sw/device/tests/sleep_pwm_pulses_test.c'
  // unit of all cycle is (CLOCK_DIV+1)
  localparam uint CLOCK_DIV = 2;
  localparam uint BEATS_PER_PULSE_CYCLE = 32;
  localparam uint CLOCK_PERIOD = (CLOCK_DIV + 1) * BEATS_PER_PULSE_CYCLE;
  // this is the duration for the active cycle [1, BEATS_PER_PULSE_CYCLE)
  // for non-invert case, duration of '1'
  rand bit[15:0] duty_cycle[NUM_PWM_CHANNELS];
  // counters for pkt stats
  uint pkt_cnt[NUM_PWM_CHANNELS]  = '{default : 0};
  uint pass_cnt[NUM_PWM_CHANNELS] = '{default : 0};
  uint fail_cnt[NUM_PWM_CHANNELS] = '{default : 0};
  uint low_power_cnt[NUM_PWM_CHANNELS] = '{default : 0};
  constraint duty_cycle_c {
    foreach (duty_cycle[i]) duty_cycle[i] inside {[1 : BEATS_PER_PULSE_CYCLE - 1]};
  }

  virtual task cpu_init();
    bit[7:0] byte_arr[];
    super.cpu_init();
    // endian swap for every word
    byte_arr = {<<8{{<<16{duty_cycle}}}};
    sw_symbol_backdoor_overwrite("kPwmDutycycle", byte_arr);
  endtask // cpu_init

  virtual task body();
    super.body();
    `uvm_info(`gfn, $sformatf("PWMSEQ : duty_cycle = %p",duty_cycle), UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "pinmux_init end")
    `uvm_info(`gfn, $sformatf("set mon active 1"), UVM_MEDIUM)
    foreach (cfg.m_pwm_monitor_cfg[i]) begin
      cfg.m_pwm_monitor_cfg[i].active = 1;
    end
    fork
      collect_pwm_data();   // this is infinite task
    join_none
  endtask // body

  virtual task post_start();
    super.post_start();
    `uvm_info(`gfn, $sformatf("set mon active 0"), UVM_MEDIUM)
    foreach (cfg.m_pwm_monitor_cfg[i]) begin
      cfg.m_pwm_monitor_cfg[i].active = 0;
      if(low_power_cnt[i] == 0) begin
        `uvm_error(`gfn,
                   $sformatf("PWMCH%0d : lowpower counter is zero", i))
      end
    end
  endtask // post_start

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
  endtask // proc_pwm_data

  virtual task process_pwm_data(int channel);
    pwm_item item;

    p_sequencer.pwm_rx_fifo[channel].get(item);
    pkt_cnt[channel]++;
    `uvm_info(`gfn, $sformatf("PWMCH%0d: got pkt %0d", channel, pkt_cnt[channel]), UVM_LOW)

    // During device init, pulse at each channel started with its
    // default value(1) at random time, which creates false
    // duration initially.
    // Flushing first 2 packets will remove such a false alarm.
    if (pkt_cnt[channel] <= 2) return;

    if (cfg.chip_vif.pwrmgr_low_power_if.low_power == 1) begin
      low_power_cnt[channel]++;
    end
    if (item.period != CLOCK_PERIOD) begin
      `uvm_error(`gfn, $sformatf("PWMCH%0d : pkt%0d Clock period is wrong.  rcv : %0d  exp : %0d",
                                 channel, pkt_cnt[channel], item.period, CLOCK_PERIOD))
    end
    if (item.active_cnt == duty_cycle_in_clk(channel)) begin
      pass_cnt[channel]++;
      `uvm_info(`gfn, $sformatf("PWMCH%0d : pkt%0d Dutycycle match.  invert : %0d  cyc : %0d",
                                channel, pkt_cnt[channel], item.invert, item.active_cnt), UVM_LOW)
    end else begin
      fail_cnt[channel]++;
      `uvm_error(`gfn,
                 $sformatf("PWMCH%0d : Dutycycle mismatch.  invert : %0d  rcv : %0d  exp : %0d",
                           channel, item.invert, item.active_cnt, duty_cycle[channel]))
    end
  endtask // process_pwm_data

  function void print_ch_cnt();
    `uvm_info(`gfn, "PWM PULSE COUNTER", UVM_LOW)
    `uvm_info(`gfn, "+----+------+------+------+-------+", UVM_LOW)
    `uvm_info(`gfn, "| CH | PASS | FAIL | LPWR | TOTAL |", UVM_LOW)

    for (int i = 0; i < NUM_PWM_CHANNELS; i++) begin
    `uvm_info(`gfn, "+----+------+------+------+-------+", UVM_LOW)
    `uvm_info(`gfn, $sformatf("+ %2d |  %2d  |  %2d  |  %2d  |  %2d   |",
        i, pass_cnt[i], fail_cnt[i], low_power_cnt[i], pkt_cnt[i] - 2), UVM_LOW)
    end
    `uvm_info(`gfn, "+----+------+------+------+-------+", UVM_LOW)
  endfunction // print_ch_cnt

  // duty_cycle_in_clk : duty_cycle * (CLOCK_DIV + 1)
  function uint duty_cycle_in_clk(int channel);
    return (duty_cycle[channel] * (CLOCK_DIV + 1));
  endfunction
endclass // chip_sw_pwm_pulses_vseq
