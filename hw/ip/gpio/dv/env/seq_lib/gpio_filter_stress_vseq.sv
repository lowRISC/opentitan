// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_filter_stress_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will the following operations:
// (  i) programs random set of interrupt registers with random values
// ( ii) programs CTRL_EN_INPUT_FILTER register to random value
// (iii) DATA_IN and INTR_STATE are read back and their read data are checked
//       aginst predicted values.
// ( iv) random noise data (data with many frequent asynchronous toggling) is
//       driven on gpio pins. After few cycles (less than FILTER_CYCLES), the
//       are toggled to original values before noise was driven. This would make
//       sure than noise filter does not see stable data on any pin long enough.
// (  v) DATA_IN and INTR_STATE are read back and their read data are checked
//       aginst predicted values.
// ( vi) Non-noise data is driven multiple times (That is, gpio pins are kept
//       stable for FILTER_CYCLES or longer). Every time after driving
//       non-noise data, registers DATA_IN and INTR_STATE are read back and
//       their read data are compared against predicted values.
class gpio_filter_stress_vseq extends gpio_intr_with_filter_rand_intr_event_vseq;

  `uvm_object_utils(gpio_filter_stress_vseq)
  `uvm_object_new

  task body();
    bit [NUM_GPIOS-1:0] gpio_i;
    bit [NUM_GPIOS-1:0] stable_value = (cfg.pullup_en) ? {NUM_GPIOS{1'b1}} : '0;
    bit [NUM_GPIOS-1:0] crnt_intr_status;
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)

    // Drive a new randomized gpio value initially for long enough
    `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
    cfg.gpio_vif.drive(gpio_i);
    // Wait for FILTER_CYCLES to make sure that we start
    // with stable gpio pins value
    cfg.clk_rst_vif.wait_clks(FILTER_CYCLES);
    stable_value = gpio_i;

    for (uint iter_num = 0; iter_num < num_trans; iter_num++) begin
      `uvm_info(`gfn, $sformatf("Start of iteration-%0d", iter_num), UVM_HIGH)

      // program filter register
      `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_filter_value)
      ral.ctrl_en_input_filter.set(gpio_filter_value);
      csr_update(ral.ctrl_en_input_filter);
      // Predict updated interrupt status register
      update_intr_state(crnt_intr_status, stable_value, stable_value);

      // program random set of interrupt registers
      pgm_intr_regs();
      // Calclulate update on interrupt state with new interrupt registers'
      // programming
      update_intr_state(crnt_intr_status, stable_value, stable_value);
      // Read and check DATA_IN and INTR_STATE registers
      read_and_check(stable_value, crnt_intr_status);

      begin : drive_noise_on_each_pin
        repeat ($urandom_range(1, 10)) begin
          for (uint pin_num = 0; pin_num  < NUM_GPIOS; pin_num++) begin
            automatic uint pin = pin_num;
            fork
              begin
                if (gpio_filter_value[pin] == 1'b1) begin
                  // Drive fully asynchronous noise for pins with filter enabled
                  drive_noise_on_pin(pin, gpio_i[pin]);
                end else begin
                  uint ps_delay;
                  bit intr_state_this_pin = crnt_intr_status[pin];
                  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ps_delay, ps_delay inside {[1:10000]};)
                  // Drive single asynchronous change for pins with filter disabled
                  #(ps_delay * 1ps);
                  cfg.gpio_vif.drive_pin(pin, ~stable_value[pin]);
                  update_pin_intr_state(pin,
                                        intr_state_this_pin,
                                        stable_value[pin],
                                        ~stable_value[pin]);
                  // update interrupt value for pin
                  crnt_intr_status[pin] = intr_state_this_pin;
                  // update stable value for pin
                  stable_value[pin] = ~stable_value[pin];
                end
              end
            join_none
          end
          wait fork;

          // Keep driving toggled value until next clock edge
          cfg.clk_rst_vif.wait_clks(1);
          // Read and check DATA_IN and INTR_STATE registers
          read_and_check(stable_value, crnt_intr_status);
        end
      end // drive_noise_on_each_pin

      // Drive some regular 'non-noise' data that stays unchanged for
      // FILTER_CYCLES or more cycles
      begin : drive_non_noise_data
        repeat ($urandom_range(1, 10)) begin
          uint num_clk_cycles;
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_clk_cycles,
                                             num_clk_cycles inside {[(FILTER_CYCLES + 1) :
                                                                     (FILTER_CYCLES + 10)]};)
           `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
           cfg.gpio_vif.drive(gpio_i);
           cfg.clk_rst_vif.wait_clks(num_clk_cycles);
           // Update predicted DATA_IN and INTR_STATE values
           update_intr_state(crnt_intr_status, stable_value, gpio_i);
           stable_value = gpio_i;
           // Read and check DATA_IN and INTR_STATE registers
           read_and_check(stable_value, crnt_intr_status);
        end
      end // drive_non_noise_data

      `uvm_info(`gfn, $sformatf("End of iteration-%0d", iter_num), UVM_HIGH)
    end // end for

  endtask : body

  task drive_noise_on_pin(input  uint pin_idx,
                          input  bit  crnt_gpio_pin_value);
    bit  pin_value = crnt_gpio_pin_value;
    uint noise_length_cycles = $urandom_range(2, FILTER_CYCLES - 1);
    bit  noise_length_cycles_done;
    uint async_drive_time_accumulated;
    uint clk_period_ps = cfg.clk_rst_vif.clk_period_ps;
    fork
      begin : keep_driving_noise
        while (async_drive_time_accumulated < (noise_length_cycles * clk_period_ps)) begin
          uint ps_delay;
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ps_delay,
              ps_delay inside {[1:((noise_length_cycles * clk_period_ps) - 1)]};)
          // Adjust ps_delay to avoid noise going beyond noise_length_cycles
          // because it causes indeterministic filtering at times and test fails
          if ((async_drive_time_accumulated + ps_delay) >
              (noise_length_cycles * clk_period_ps) ) begin
            ps_delay = (noise_length_cycles * clk_period_ps) - async_drive_time_accumulated;
          end
          // Add ps_delay to async_drive_time_accumulated
          async_drive_time_accumulated += ps_delay;
          // Wait for ps_delay
          #(ps_delay * 1ps);
          // Re-check if wait_noise_length_cycles thread has meanwhile finished
          if (async_drive_time_accumulated < (noise_length_cycles * clk_period_ps)) begin
            pin_value = ~pin_value;
            cfg.gpio_vif.drive_pin(pin_idx, pin_value);
          end
        end
      end
      begin : wait_noise_length_cycles
        cfg.clk_rst_vif.wait_clks(noise_length_cycles);
        noise_length_cycles_done = 1'b1;
      end
    join
    // Drive original pin value again
    cfg.gpio_vif.drive_pin(pin_idx, crnt_gpio_pin_value);
  endtask : drive_noise_on_pin

  function void update_pin_intr_state(input uint pin_idx,
                                      ref   bit  pin_current_interrupt_state,
                                      input bit  pin_prev_filtered_value,
                                      input bit  pin_crnt_exp_filtered_value);
    bit [NUM_GPIOS-1:0] intr_ctrl_en_rising  = ral.intr_ctrl_en_rising.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_falling = ral.intr_ctrl_en_falling.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvlhigh = ral.intr_ctrl_en_lvlhigh.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvllow  = ral.intr_ctrl_en_lvllow.get();
    bit new_intr_state_updates;

    // Look for edge triggered interrupts
    if (pin_crnt_exp_filtered_value != pin_prev_filtered_value) begin
      if (((pin_prev_filtered_value == 1'b0 && pin_crnt_exp_filtered_value == 1'b1) &&
           intr_ctrl_en_rising[pin_idx] == 1'b1) ||
          ((pin_prev_filtered_value == 1'b1 && pin_crnt_exp_filtered_value == 1'b0) &&
           intr_ctrl_en_falling[pin_idx] == 1'b1)) begin
        new_intr_state_updates = 1'b1;
      end
    end
    // Look for level triggerred interrupts
    if (new_intr_state_updates == 1'b0) begin
      if ((pin_crnt_exp_filtered_value == 1'b1 && intr_ctrl_en_lvlhigh[pin_idx]) ||
          (pin_crnt_exp_filtered_value == 1'b0 && intr_ctrl_en_lvllow[pin_idx])) begin
        new_intr_state_updates = 1'b1;
      end
    end
    // Update interrupt value for pin_idx
    pin_current_interrupt_state |= new_intr_state_updates;
  endfunction : update_pin_intr_state

  task read_and_check(bit [NUM_GPIOS-1:0] predicted_data_in,
                      bit [NUM_GPIOS-1:0] predicted_intr_state);
    // Read DATA_IN and check if predictaed and actual values match
    csr_rd_check(.ptr(ral.data_in), .compare_value(predicted_data_in));
    // Read interrupt value after noise driving is finished
    csr_rd_check(.ptr(ral.intr_state), .compare_value(predicted_intr_state));
  endtask : read_and_check

endclass : gpio_filter_stress_vseq
