// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class gpio_scoreboard extends cip_base_scoreboard #(.CFG_T (gpio_env_cfg),
                                                    .RAL_T (gpio_reg_block),
                                                    .COV_T (gpio_env_cov));

  // predicted value of DATA_OUT rtl implementation register
  bit   [NUM_GPIOS-1:0] data_out;
  // predicted updated value of DATA_OE rtl implementation register
  bit   [NUM_GPIOS-1:0] data_oe;
  // input presented by driving gpio_i
  logic [NUM_GPIOS-1:0] gpio_i_driven;
  // Flag to store value to be updated for INTR_STATE register
  // and to indicate whether value change is due currently
  gpio_reg_update_due intr_state_update_due;

  `uvm_component_utils(gpio_scoreboard)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    monitor_gpio_i();
  endtask

  // task : process_tl_access
  // process monitored tl transaction
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit do_read_check       = 1'b1;
    bit write               = item.is_write();
    uvm_reg_addr_t csr_addr = {item.a_addr[TL_AW-1:2], 2'b00};

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    if (csr == null) begin
      // we hit an oob addr - expect error response and return
      `DV_CHECK_EQ(item.d_error, 1'b1)
      return;
    end

    // grab completed transactions from data channel; ignore packets from address channel
    if (channel == AddrChannel) begin
      // apply pending update for interrupt stste
      if (intr_state_update_due.need_update == 1'b1) begin
        ral.intr_state.predict(.value(intr_state_update_due.reg_value),
                               .kind(UVM_PREDICT_READ));
        `uvm_info(`gfn, $sformatf("Predicted intr_state with value %0h",
                                  intr_state_update_due.reg_value), UVM_HIGH)
        intr_state_update_due.need_update = 1'b0;
        intr_state_update_due.reg_value = '0;
      end
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask));
        `uvm_info(`gfn, "Calling gpio_predict_and_compare on reg write", UVM_HIGH)
        gpio_predict_and_compare(csr);
      end
    end else begin // if (channel == DataChannel)
      if (write == 0) begin
        // If do_read_check, is set, then check mirrored_value against item.d_data
        if (do_read_check) begin
          // Checker-2: Check for correctness of "data_in" register read data
          if (csr.get_name() == "data_in") begin
            `DV_CHECK_CASE_EQ(item.d_data, cfg.gpio_vif.pins);
          end else if (csr.get_name() == "intr_state") begin
            `DV_CHECK_EQ(item.d_data, csr.get_mirrored_value())
          end
          // Checker-3: Check if reg read data matches expected value or not
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
        end
      end
    end
  endtask : process_tl_access

  // Task : monitor_gpio_i
  // monitor gpio input pins interface
  virtual task monitor_gpio_i();
    logic [NUM_GPIOS-1:0] prev_gpio_i = (cfg.active_high_pullup) ? {NUM_GPIOS{1'b1}} : '0;

    forever begin : monitor_pins_if
      @(cfg.gpio_vif.pins or under_reset);
      if (under_reset == 1'b0) begin
        // evaluate gpio input driven to dut
        foreach (cfg.gpio_vif.pins_oe[pin_num]) begin
          if (cfg.gpio_vif.pins_oe[pin_num] == 1'b1) begin
            gpio_i_driven[pin_num] = cfg.gpio_vif.pins_o[pin_num];
          end else begin
            gpio_i_driven[pin_num] = 1'bz;
          end
          `uvm_info(`gfn, $sformatf("pins_oe[%0d] = %0b pins_o[%0d] = %0b gpio_i_driven[%0d] = %0b",
                                    pin_num, cfg.gpio_vif.pins_oe[pin_num], pin_num,
                                    cfg.gpio_vif.pins_o[pin_num], pin_num, gpio_i_driven[pin_num]),
                                    UVM_HIGH)
        end

        `uvm_info(`gfn, $sformatf("pins = 0x%0h [%0b]) gpio_i_driven = 0x%0h [%0b]",
                                  cfg.gpio_vif.pins, cfg.gpio_vif.pins, gpio_i_driven,
                                  gpio_i_driven), UVM_HIGH)
        // Predict effect on gpio pins
        gpio_predict_and_compare();

        if (prev_gpio_i !== cfg.gpio_vif.pins) begin
          // Flag to indicate:
          // (i) if there was any change in value on gpio_i pin - Bit0
          // (ii) what change occurred on gpio_i pin - Bit1
          gpio_transition [NUM_GPIOS-1:0] gpio_i_transition;
          foreach (prev_gpio_i[pin]) begin
            gpio_i_transition[pin].transition = cfg.gpio_vif.pins[pin] !== prev_gpio_i[pin];
            if (gpio_i_transition[pin].transition) begin
              case (cfg.gpio_vif.pins[pin])
                1'b0: begin
                  // Negedge seen on pin, indicated by 0 value
                  gpio_i_transition[pin].rose_or_fell = 1'b0;
                end
                1'b1: begin
                  // Posedge seen on pin, indicated by 1 value
                  gpio_i_transition[pin].rose_or_fell = 1'b1;
                end
                1'bz: begin
                  if (prev_gpio_i[pin] === 1'b1) begin
                    // Negedge seen on pin, indicated by 0 value
                    gpio_i_transition[pin].rose_or_fell = 1'b0;
                  end else if (prev_gpio_i[pin] === 1'b0) begin
                    // Posedge seen on pin, indicated by 1 value
                    gpio_i_transition[pin].rose_or_fell = 1'b1;
                  end else begin
                    // x->z does not indicate useful transition, reset transition bit
                    gpio_i_transition[pin].transition = 1'b0;
                  end
                end
                1'bx: begin
                  if (prev_gpio_i[pin] === 1'b1) begin
                    // Negedge seen on pin, indicated by 0 value
                    gpio_i_transition[pin].rose_or_fell = 1'b0;
                  end else if (prev_gpio_i[pin] === 1'b0) begin
                    // Posedge seen on pin, indicated by 1 value
                    gpio_i_transition[pin].rose_or_fell = 1'b1;
                  end else begin
                    // z->x does not indicate useful transition, reset transition bit
                    gpio_i_transition[pin].transition = 1'b0;
                  end
                end
              endcase
            end
          end
          foreach (gpio_i_transition[ii]) begin
            `uvm_info(`gfn, $sformatf("gpio_i_transition[%0d] = %0p", ii, gpio_i_transition[ii]),
                      UVM_HIGH)
          end
          // Look for interrupt event and update interrupt status
          gpio_interrupt_predict(gpio_i_transition);
          // Update value
          prev_gpio_i = cfg.gpio_vif.pins;
        end
      end

    end // monitor_pins_if

  endtask : monitor_gpio_i

  // function : gpio_predict_and_compare
  function void gpio_predict_and_compare(uvm_reg csr = null);
    string msg_id = {`gfn, " gpio_predict_and_compare: "};
    // Predicted value of "pins" from within gpio_vif
    logic [NUM_GPIOS-1:0] pred_val_gpio_pins;
    // Flag to decide if gpio data prediction and check are required
    bit gpio_data_check = 1'b1;

    if (csr != null) begin
      // process the csr req
      case (csr.get_name())
        "data_in": begin
          gpio_data_check = 1'b0;
        end
        "direct_out": begin
          data_out = csr.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
                    UVM_HIGH)
          // Update mirror values of *out* registers
          update_gpio_out_regs();
        end
        "masked_out_lower": begin
          uvm_reg_data_t mask = ral.masked_out_lower.mask.get_mirrored_value();
          uvm_reg_data_t data = ral.masked_out_lower.data.get_mirrored_value();

          for (uint pin_idx = 0;
               pin_idx < ral.masked_out_lower.mask.get_n_bits(); pin_idx++) begin
            if (mask[pin_idx] == 1'b1) begin
              data_out[pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
                    UVM_HIGH)
          // Update mirror values of *out* registers
          update_gpio_out_regs();
        end
        "masked_out_upper": begin
          uvm_reg_data_t mask = ral.masked_out_upper.mask.get_mirrored_value();
          uvm_reg_data_t data = ral.masked_out_upper.data.get_mirrored_value();

          for (uint pin_idx = 0; pin_idx < ral.masked_out_upper.mask.get_n_bits(); pin_idx++) begin
            if (mask[pin_idx] == 1'b1) begin
              data_out[(NUM_GPIOS / 2) + pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
                    UVM_HIGH)
          // Update mirror values of *out* registers
          update_gpio_out_regs();
        end
        "direct_oe": begin
          data_oe = csr.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
                    UVM_HIGH)
          // Update mirror values of *oe* registers
          update_gpio_oe_regs();
        end
        "masked_oe_lower": begin
          uvm_reg_data_t mask = ral.masked_oe_lower.mask.get_mirrored_value();
          uvm_reg_data_t data = ral.masked_oe_lower.data.get_mirrored_value();

          for (uint pin_idx = 0; pin_idx < ral.masked_oe_lower.mask.get_n_bits(); pin_idx++) begin
            if (mask[pin_idx] == 1'b1) begin
              data_oe[pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_oe reg updated to 0x%0h [%0b]", data_oe, data_oe),
                    UVM_HIGH)
          // Update mirror values of *oe* registers
          update_gpio_oe_regs();
        end
        "masked_oe_upper": begin
          uvm_reg_data_t mask = ral.masked_oe_upper.mask.get_mirrored_value();
          uvm_reg_data_t data = ral.masked_oe_upper.data.get_mirrored_value();

          for (uint pin_idx = 0; pin_idx < ral.masked_oe_upper.mask.get_n_bits(); pin_idx++) begin
            if (mask[pin_idx] == 1'b1) begin
              data_oe[(NUM_GPIOS / 2) + pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_oe reg updated to %0h", data_oe), UVM_HIGH)
          // Update mirror values of *oe* registers
          update_gpio_oe_regs();
        end
        "intr_enable": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_state": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_test": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_ctrl_en_rising": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_ctrl_en_falling": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_ctrl_en_lvlhigh": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "intr_ctrl_en_lvllow": begin
          gpio_data_check = 1'b0;
          gpio_interrupt_predict();
        end
        "ctrl_en_input_filter": begin
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    // GPIO inout signal value check
    if (gpio_data_check == 1'b1) begin
      // effect of gpio_o on gpio_i based on gpio_oe
      logic [NUM_GPIOS-1:0] data_out_effect_on_gpio_i;
      // As there is a common net that drives gpio_i and gets driven through gpio_o
      // based on gpio_oe, gpio_i will have effect of (gpio_o & gpio_oe) value
      foreach (data_oe[pin_num]) begin
        if (data_oe[pin_num] === 1'b1) begin
          data_out_effect_on_gpio_i[pin_num] = data_out[pin_num];
        end else begin
          data_out_effect_on_gpio_i[pin_num] = 1'bz;
        end
      end
      `uvm_info(msg_id, $sformatf("data_out_effect_on_gpio_i = 0x%0h [%0b]",
                                  data_out_effect_on_gpio_i, data_out_effect_on_gpio_i), UVM_HIGH)

      // TODO-Should we have a logic for 'x' and 'z' values of data_oe[pin_num]?

      // Predict effective value of common wire that-
      // (i) drives gpio_i, and
      // (ii) gets driven by gpio_o based on gpiooe value
      for (uint pin_num = 0; pin_num < NUM_GPIOS; pin_num++) begin
        if (data_out_effect_on_gpio_i[pin_num] === 1'bz) begin
          pred_val_gpio_pins[pin_num] = gpio_i_driven[pin_num];
        end
        else if (gpio_i_driven[pin_num] === 1'bz) begin
          pred_val_gpio_pins[pin_num] = data_out_effect_on_gpio_i[pin_num];
        end
        else if (data_out_effect_on_gpio_i[pin_num] === gpio_i_driven[pin_num]) begin
          pred_val_gpio_pins[pin_num] = data_out_effect_on_gpio_i[pin_num];
        end
        else begin
          pred_val_gpio_pins[pin_num] = 1'bx;
        end
        if (pred_val_gpio_pins[pin_num] === 1'bz && cfg.active_high_pullup == 1'b1) begin
          pred_val_gpio_pins[pin_num] = 1'b1;
        end
      end
      `uvm_info(msg_id, $sformatf("pred_val_gpio_pins = %0h(%0b)", pred_val_gpio_pins,
                                  pred_val_gpio_pins), UVM_HIGH)

      // Update data_in register value based on result of input and output
      ral.data_in.data_in.predict(.value(pred_val_gpio_pins), .kind(UVM_PREDICT_DIRECT));
      // Checker-1: Compare predicted and actual values of gpio pins
      // Avoid calling this checker due to weak pull-up effect
      if ( (|gpio_i_driven === 1'b1) || (csr != null) ) begin
        `DV_CHECK_CASE_EQ(pred_val_gpio_pins, cfg.gpio_vif.pins)
      end
    end

  endfunction : gpio_predict_and_compare

  // Function : gpio_interrupt_predict
  // This function computes expected value of gpio intr_status based on
  // changes of gpio_i data or interrupt control registers
  virtual function void gpio_interrupt_predict(
    input gpio_transition [NUM_GPIOS-1:0] gpio_i_transition = {NUM_GPIOS{2'b00}});

    string msg_id = {`gfn, $sformatf(" gpio_interrupt_predict: ")};
    bit [NUM_GPIOS-1:0] intr_state           = ral.intr_state.get_mirrored_value();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_rising  = ral.intr_ctrl_en_rising.get_mirrored_value();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_falling = ral.intr_ctrl_en_falling.get_mirrored_value();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvlhigh = ral.intr_ctrl_en_lvlhigh.get_mirrored_value();
    bit [NUM_GPIOS-1:0] intr_ctrl_en_lvllow  = ral.intr_ctrl_en_lvllow.get_mirrored_value();
    // expected(predicted) value of interrupt status
    bit [NUM_GPIOS-1:0] exp_intr_status;

    `uvm_info(msg_id, $sformatf("intr_state = 0x%0h [%0b]",
                                intr_state, intr_state), UVM_HIGH)
    // Check if there is already INTR_STATE value update which was already due
    // for update, but not actually updated
    if (intr_state_update_due.need_update) begin
      intr_state = intr_state_update_due.reg_value;
      `uvm_info(msg_id, $sformatf("intr_state after update = 0x%0h [%0b]",
                                  intr_state, intr_state), UVM_HIGH)
    end

    // TODO-Remove displays once logic is proven
    `uvm_info(msg_id, $sformatf("intr_ctrl_en_lvllow = 0x%0h [%0b]",
                                intr_ctrl_en_lvllow, intr_ctrl_en_lvllow), UVM_HIGH)
    `uvm_info(msg_id, $sformatf("intr_ctrl_en_lvlhigh = 0x%0h [%0b]",
                                intr_ctrl_en_lvlhigh, intr_ctrl_en_lvlhigh), UVM_HIGH)
    `uvm_info(msg_id, $sformatf("intr_ctrl_en_falling = 0x%0h [%0b]",
                                intr_ctrl_en_falling, intr_ctrl_en_falling), UVM_HIGH)
    `uvm_info(msg_id, $sformatf("intr_ctrl_en_rising = 0x%0h [%0b]",
                                intr_ctrl_en_rising, intr_ctrl_en_rising), UVM_HIGH)
    // 1. Look for edge triggerred interrupts
    if (gpio_i_transition != {NUM_GPIOS{2'b00}}) begin
      foreach (gpio_i_transition[each_pin]) begin
        if (gpio_i_transition[each_pin].transition) begin
          if ((gpio_i_transition[each_pin].rose_or_fell == 1'b0 &&
               intr_ctrl_en_falling[each_pin] == 1'b1) ||
              (gpio_i_transition[each_pin].rose_or_fell == 1'b1 &&
               intr_ctrl_en_rising[each_pin] == 1'b1))
              begin
            exp_intr_status[each_pin] = 1'b1;
          end else begin
            exp_intr_status[each_pin] = intr_state[each_pin];
          end
        end
      end
    end
    // 2. Look for level triggerred interrupts
    for (uint each_pin = 0; each_pin < TL_DW; each_pin++) begin
      if (exp_intr_status[each_pin] == 1'b0) begin
        if ((cfg.gpio_vif.pins[each_pin] == 1'b1 && intr_ctrl_en_lvlhigh[each_pin] == 1'b1) ||
            (cfg.gpio_vif.pins[each_pin] == 1'b0 && intr_ctrl_en_lvllow[each_pin] == 1'b1)) begin
          exp_intr_status[each_pin] = 1'b1;
        end else begin
          exp_intr_status[each_pin] = intr_state[each_pin];
        end
      end
      else begin
        `uvm_info(msg_id, $sformatf("exp_intr_status[%0d] is already asserted", each_pin), UVM_HIGH)
      end
    end
    `uvm_info(msg_id, $sformatf("Predicted interrupt status = 0x%0h [%0b]",
                                exp_intr_status, exp_intr_status), UVM_HIGH)
    // Keep update pending until register access is done
    intr_state_update_due.need_update = 1'b1;
    intr_state_update_due.reg_value = exp_intr_status;
  endfunction : gpio_interrupt_predict

  // Function : update_gpio_out_regs
  // This function is used for updating direct_out, masked_out_upper and masked_out_lower
  // register values based on write to any one of these 3 registers.
  // Note : Assumption for this method is that data_out has already been updated
  //        before calling the method.
  function void update_gpio_out_regs();
    uvm_reg_data_t data;
    const uvm_reg_data_t mask = 0;
    // 1. Update "direct_out" register for writes to masked_out_* registers
    //    For write to "direct_out", it must have been updated already.
    ral.direct_out.predict(.value(data_out), .kind(UVM_PREDICT_WRITE));
    // 2. Update masked_out_lower
    data = data_out;
    for (uint idx = ral.masked_out_lower.data.get_n_bits();
         idx < `UVM_REG_DATA_WIDTH;
         idx++) begin
      data[idx] = 1'b0;
    end
    ral.masked_out_lower.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE));
    ral.masked_out_lower.data.predict(.value(data), .kind(UVM_PREDICT_WRITE));
    // 3. Update masked_out_upper
    data = 0;
    for (uint idx = ral.masked_out_upper.data.get_n_bits();
         idx < `UVM_REG_DATA_WIDTH;
         idx++) begin
      data[idx - ral.masked_out_upper.data.get_n_bits()] = data_out[idx];
    end
    ral.masked_out_upper.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE));
    ral.masked_out_upper.data.predict(.value(data), .kind(UVM_PREDICT_WRITE));
  endfunction : update_gpio_out_regs

  // Function : update_gpio_oe_regs
  // This function is used for updating direct_oe, masked_oe_upper and masked_oe_lower
  // register values based on write to any one of these 3 registers.
  // Note : Assumption for this method is that data_oe has already been updated
  //        before calling the method.
  function void update_gpio_oe_regs();
    uvm_reg_data_t data;
    const uvm_reg_data_t mask = 0;
    // 1. Update "direct_oe" register for writes to masked_oe_* registers
    //    For write to "direct_oe", it must have been updated already.
    ral.direct_oe.predict(.value(data_oe), .kind(UVM_PREDICT_WRITE));
    // 2. Update masked_oe_lower
    data = data_oe;
    for (uint idx = ral.masked_oe_lower.data.get_n_bits(); idx < `UVM_REG_DATA_WIDTH; idx++) begin
      data[idx] = 1'b0;
    end
    ral.masked_oe_lower.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE));
    ral.masked_oe_lower.data.predict(.value(data), .kind(UVM_PREDICT_WRITE));
    // 3. Update masked_oe_upper
    data = 0;
    for (uint idx = ral.masked_oe_upper.data.get_n_bits(); idx < `UVM_REG_DATA_WIDTH; idx++) begin
      data[idx - ral.masked_oe_upper.data.get_n_bits()] = data_oe[idx];
    end
    ral.masked_oe_upper.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE));
    ral.masked_oe_upper.data.predict(.value(data), .kind(UVM_PREDICT_WRITE));
  endfunction : update_gpio_oe_regs

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

endclass : gpio_scoreboard
