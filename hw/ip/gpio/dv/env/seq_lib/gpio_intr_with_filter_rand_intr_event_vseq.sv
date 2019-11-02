// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// class : gpio_intr_with_filter_rand_intr_event_vseq
// This gpio random test sequence performs random no. of iteration such that
// each iteration will the following operations:
// (  i) programs random set of interrupt registers with random values
// ( ii) optionally, programs CTRL_EN_INPUT_FILTER register to random value
// (iii) drives random gpio input data values while gpio outputs are disabled,
//      such that different pins changes value at random number of cycles
//      selected within [1:15] range, or stays same for 16 cycles.
//  This test sequence reads DATA_IN and INTR_STATE register multiple times
//  and every time, it checks for corresponding expected register value.
class gpio_intr_with_filter_rand_intr_event_vseq extends gpio_base_vseq;

  // Random variable to specify for how many cycles one would like to keep
  // gpio input pin value stable
  rand uint stable_cycles_per_pin [NUM_GPIOS];

  // Filter enable value
  bit [TL_DW-1:0] gpio_filter_value;

  constraint stable_cycles_for_input_c {
    foreach (stable_cycles_per_pin[i])
      stable_cycles_per_pin[i] dist { [1:FILTER_CYCLES-1] :/ 70,
                                            FILTER_CYCLES :/ 30 };
  }

  covergroup pins_stable_period_and_filter_cg with function sample(uint pin,
                                                                   uint stable_cycles,
                                                                   bit pin_value,
                                                                   bit filter_en);
    cp_pins: coverpoint pin {
      bins all_gpio_pins[] = {[0:NUM_GPIOS-1]};
    }
    cp_stable_cycles: coverpoint stable_cycles {
      bins one_to_filter_cycles_minus_1[] = {[1:FILTER_CYCLES - 1]};
      bins filter_cycles_or_more          = {[FILTER_CYCLES:$]};
    }
    cp_pin_value: coverpoint pin_value;
    cp_filter_en: coverpoint filter_en;
    cp_cross: cross cp_pins, cp_stable_cycles, cp_pin_value, cp_filter_en;
  endgroup : pins_stable_period_and_filter_cg

  `uvm_object_utils(gpio_intr_with_filter_rand_intr_event_vseq)

  function new(string name = "gpio_intr_with_filter_rand_intr_event_vseq");
    super.new(name);
    pins_stable_period_and_filter_cg = new();
  endfunction : new

  task sample_stable_cycles_and_filter_coverage();
    // Sampling coverage related to gpio pins' stable cycles
    bit [NUM_GPIOS-1:0] prev_pins_val = (cfg.pullup_en == 1'b1) ? '1 : '0;
    bit [NUM_GPIOS-1:0] crnt_pins_val;
    uint stable_cycles_cnt[NUM_GPIOS];
    forever @(cfg.clk_rst_vif.cb) begin
      // Assign current sampled gpio value
      crnt_pins_val = cfg.gpio_vif.sample();
      foreach (crnt_pins_val[each_pin]) begin
        if (crnt_pins_val[each_pin] == prev_pins_val[each_pin]) begin
          stable_cycles_cnt[each_pin]++;
        end else begin
          stable_cycles_cnt[each_pin] = 1;
        end
        pins_stable_period_and_filter_cg.sample(each_pin,
                                                stable_cycles_cnt[each_pin],
                                                crnt_pins_val[each_pin],
                                                gpio_filter_value[each_pin]);
      end
      // Update previous gpio value
      prev_pins_val = crnt_pins_val;
    end
  endtask : sample_stable_cycles_and_filter_coverage

  task body();
    bit [NUM_GPIOS-1:0] gpio_i;
    bit [NUM_GPIOS-1:0] stable_value = (cfg.pullup_en) ? {NUM_GPIOS{1'b1}} : '0;
    bit [TL_DW-1:0] crnt_intr_status;
    `uvm_info(`gfn, $sformatf("num_trans = %0d", num_trans), UVM_HIGH)
    // Wait for FILTER_CYCLES to make sure that we start
    // with stable gpio pins value
    cfg.clk_rst_vif.wait_clks(FILTER_CYCLES);

    // Sample coverage for pins' stable cycles and filter
    if (cfg.en_cov) begin
      fork
        sample_stable_cycles_and_filter_coverage();
      join_none
    end

    for (uint tr_num = 0; tr_num < num_trans; tr_num++) begin
      string msg_id = {`gfn, $sformatf(" Transaction-%0d", tr_num)};
      uint tmp_q[$];
      // Minimum no. of cycles required after driving is done, to have
      // get GPIO pins with stable and updated value with noise filter
      uint additional_clk_cycles_until_all_gpio_pins_stable;
      // Maximum no. of stable cycles among all the pins
      uint max_stable_cycles;

      `uvm_info(msg_id, $sformatf("crnt_intr_status = 0x%0h [%0b]",
                                  crnt_intr_status, crnt_intr_status), UVM_HIGH)
      // Program random set of interrupt registers
      pgm_intr_regs();
      // Predict updated interrupt status register
      update_intr_state(crnt_intr_status, stable_value, stable_value);
      // Program filter register
      if ($urandom_range(0, 1)) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_filter_value)
        ral.ctrl_en_input_filter.set(gpio_filter_value);
        csr_update(ral.ctrl_en_input_filter);
      end
      `uvm_info(msg_id, $sformatf("gpio_filter_value = 0x%0h [%0b]",
                                  gpio_filter_value, gpio_filter_value), UVM_HIGH)
      // Predict updated interrupt status register again
      update_intr_state(crnt_intr_status, stable_value, stable_value);
      // Randomize gpio data
      `DV_CHECK_STD_RANDOMIZE_FATAL(gpio_i)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(stable_cycles_per_pin)
      foreach (stable_cycles_per_pin[each_pin]) begin
        if (gpio_filter_value[each_pin] == 0) begin
          stable_cycles_per_pin[each_pin] = FILTER_CYCLES;
        end
      end
      `uvm_info(`gfn, $sformatf("stable_cycles_per_pin = %0p", stable_cycles_per_pin), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("gpio_i = 0x%0h [%0b]", gpio_i, gpio_i), UVM_HIGH)
      // Calculate additional_clk_cycles_until_all_gpio_pins_stable
      tmp_q = stable_cycles_per_pin.find(m) with (m != FILTER_CYCLES);
      tmp_q.rsort();
      additional_clk_cycles_until_all_gpio_pins_stable = tmp_q[0];
      // Find maximum stable cycles among all pins
      tmp_q.delete();
      tmp_q = stable_cycles_per_pin;
      tmp_q.rsort();
      max_stable_cycles = tmp_q[0];
      // Program direct_oe to all 0's
      if (tr_num == 0) begin
        ral.direct_oe.set('0);
        csr_update(ral.direct_oe);
      end

      `uvm_info(msg_id, "Start driving new random value in gpio_i", UVM_HIGH)
      fork
        begin : drive_each_pin
          for (uint pin_num = 0; pin_num  < NUM_GPIOS; pin_num++) begin
            automatic uint pin = pin_num;
            fork
              begin
                cfg.gpio_vif.pins_oe[pin] = 1'b1;
                cfg.gpio_vif.pins_o[pin] = gpio_i[pin];
                // When filter is not enabled, keep value stable
                cfg.clk_rst_vif.wait_clks(stable_cycles_per_pin[pin]);
                // Toggle pin if stable cycles are less than FILTER_CYCLES
                if (stable_cycles_per_pin[pin] < FILTER_CYCLES) begin
                  cfg.gpio_vif.pins_o[pin] = ~gpio_i[pin];
                end
              end
            join_none
          end
          wait fork;

          // If one of more pins had FILTER_CYCLES no. of stable cycles,
          // expect those pins' gpio_i data to be filtered out and hence
          // interrupt update is expected
          if (max_stable_cycles == FILTER_CYCLES) begin
            bit [NUM_GPIOS-1:0] latest_stable_value = stable_value;
            foreach (stable_cycles_per_pin[pin]) begin
              if (stable_cycles_per_pin[pin] == FILTER_CYCLES) begin
                latest_stable_value[pin] = gpio_i[pin];
              end
            end
            update_intr_state(crnt_intr_status, stable_value, latest_stable_value);
            stable_value = latest_stable_value;
            `uvm_info(msg_id, $sformatf("stable_value updated to %0h", stable_value), UVM_HIGH)
          end
        end // drive_each_pin

        begin : csr_read_and_check
          uint num_cycles_elapsed;
          bit [NUM_GPIOS-1:0] expected_value_data_in = predict_data_in_value(gpio_filter_value,
                                                                             stable_value,
                                                                             gpio_i);
          // Predict updated interrupt status register again
          update_intr_state(crnt_intr_status, stable_value, expected_value_data_in);
          `uvm_info(msg_id, $sformatf("crnt_intr_status = 0x%0h [%0b]",
                                      crnt_intr_status, crnt_intr_status), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("Expected data in = 0x%0h [%0b]",
                                    expected_value_data_in, expected_value_data_in), UVM_HIGH)
          fork
            begin : count_clock
              while (num_cycles_elapsed < FILTER_CYCLES) begin
                cfg.clk_rst_vif.wait_clks(1);
                num_cycles_elapsed++;
              end // count_clock
            end
            begin : csr_rd_and_check
              // Actual rtl register update takes additional cycle
              // So if we read DATA_IN or INTR_STATE register immediately on
              // subsequent clock cycle of write, we may still get older value
              cfg.clk_rst_vif.wait_clks(1);
              do begin
                randcase
                  3: csr_rd_check(.ptr(ral.intr_state), .compare_value(crnt_intr_status));
                  1: csr_rd_check(.ptr(ral.data_in), .compare_value(expected_value_data_in));
                endcase
              end
              while (num_cycles_elapsed < (FILTER_CYCLES -2));
            end // csr_rd_and_check
          join // end fork..join
        end // csr_read_and_check

      join

      begin : wait_all_pins_stable
        uint cycles_after_16_per_pin[NUM_GPIOS];
        bit [NUM_GPIOS-1:0] latest_stable_value = stable_value;
        repeat (additional_clk_cycles_until_all_gpio_pins_stable) begin
          cfg.clk_rst_vif.wait_clks(1);
          `uvm_info(msg_id, "After one clock cycle", UVM_HIGH)
          foreach (stable_cycles_per_pin[pin]) begin
            cycles_after_16_per_pin[pin]++;
            if (cycles_after_16_per_pin[pin] == stable_cycles_per_pin[pin]) begin
              latest_stable_value[pin] = ~gpio_i[pin];
              `uvm_info(msg_id, $sformatf("updating latest_stable_value[%0d] to %0b",
                                          pin, latest_stable_value[pin]), UVM_HIGH)
            end
          end
          // Check for interrupt update based on stabilized pin
          update_intr_state(crnt_intr_status, stable_value, latest_stable_value);
          stable_value = latest_stable_value;
        end
        // Additional cycle for rtl to latch updated DATA_IN and INTR_STATE values
        cfg.clk_rst_vif.wait_clks(1);
        stable_value = cfg.gpio_vif.pins;
        // Predict updated interrupt status register again
        update_intr_state(crnt_intr_status, stable_value, stable_value);
        // Read and check DATA_IN value
        csr_rd_check(.ptr(ral.data_in), .compare_value(stable_value));
        // Read and check INTR_STATE value
        csr_rd_check(.ptr(ral.intr_state), .compare_value(crnt_intr_status));
      end // wait_all_pins_stable

      `uvm_info(msg_id, "End of Transaction", UVM_HIGH)

    end // end for

  endtask : body

  // Function: predict_data_in_value
  // This function considers current 'unfiltered' value of gpio_i and
  // predicts expected effective data_in value based on following:
  // ( i) noise filter programming, and
  // (ii) previous filtered value
  function bit [NUM_GPIOS-1:0] predict_data_in_value(
    input bit [    TL_DW-1:0] filter_en,
    input bit [NUM_GPIOS-1:0] crnt_filtered_value,
    input bit [NUM_GPIOS-1:0] gpio_i);
    string msg_id = {`gfn, " predict_data_in_value: "};
    for (uint i = 0; i < NUM_GPIOS; i++) begin
      predict_data_in_value[i] = filter_en[i] ? crnt_filtered_value[i] : gpio_i[i];
      `uvm_info(msg_id, { $sformatf("pin-%0d filter_en[%0d] = %0b", i, i, filter_en[i]),
                          $sformatf("crnt_filtered_value[%0d] = %0b", i, crnt_filtered_value[i]),
                          $sformatf("gpio_i[%0d] = %0b", i, gpio_i[i]) }, UVM_HIGH)
    end
  endfunction : predict_data_in_value

  // Function: update_intr_state
  // This function takes current interrupt state as reference, and calculates
  // updated interrupt state value based on following:
  // (i) interrupt control registers' values
  // (ii) previous filtered gpio value
  // (iii) currently filtered gpio value
  function void update_intr_state(  ref bit [    TL_DW-1:0] current_interrupt_state,
                                  input bit [NUM_GPIOS-1:0] prev_filtered_value,
                                  input bit [NUM_GPIOS-1:0] crnt_exp_filtered_value);
    bit [NUM_GPIOS-1:0] intr_ctrl_en_rising  = ral.intr_ctrl_en_rising.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_falling = ral.intr_ctrl_en_falling.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvlhigh = ral.intr_ctrl_en_lvlhigh.get();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvllow  = ral.intr_ctrl_en_lvllow.get();
    bit [TL_DW-1:0] new_intr_state_updates;

    foreach (crnt_exp_filtered_value[pin]) begin
      // Look for edge triggered interrupts
      if (crnt_exp_filtered_value[pin] != prev_filtered_value[pin]) begin
        if (((prev_filtered_value[pin] == 1'b0 && crnt_exp_filtered_value[pin] == 1'b1) &&
             intr_ctrl_en_rising[pin] == 1'b1) ||
            ((prev_filtered_value[pin] == 1'b1 && crnt_exp_filtered_value[pin] == 1'b0) &&
             intr_ctrl_en_falling[pin] == 1'b1)) begin
          new_intr_state_updates[pin] = 1'b1;
        end
      end
      // Look for level triggerred interrupts
      if (new_intr_state_updates[pin] == 1'b0) begin
        if ((crnt_exp_filtered_value[pin] == 1'b1 && intr_ctrl_en_lvlhigh[pin]) ||
            (crnt_exp_filtered_value[pin] == 1'b0 && intr_ctrl_en_lvllow[pin])) begin
          new_intr_state_updates[pin] = 1'b1;
        end
      end
      // Update interrupt value for pin
      current_interrupt_state[pin] |= new_intr_state_updates[pin];
    end
  endfunction : update_intr_state

endclass : gpio_intr_with_filter_rand_intr_event_vseq
