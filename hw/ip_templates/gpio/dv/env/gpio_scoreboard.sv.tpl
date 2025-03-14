// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class ${module_instance_name}_scoreboard extends cip_base_scoreboard #(.CFG_T (${module_instance_name}_env_cfg),
                                                    .RAL_T (${module_instance_name}_reg_block),
                                                    .COV_T (${module_instance_name}_env_cov));

  // predicted value of DATA_OUT rtl implementation register
  bit   [NUM_GPIOS-1:0] data_out;
  // predicted updated value of DATA_OE rtl implementation register
  bit   [NUM_GPIOS-1:0] data_oe;
  // input presented by driving ${module_instance_name}_i
  logic [NUM_GPIOS-1:0] ${module_instance_name}_i_driven;
  // ${module_instance_name} input pins if previous out value
  logic [NUM_GPIOS-1:0] prv_${module_instance_name}_i_pins_o;
  // ${module_instance_name} input pins if previous out enable value
  logic [NUM_GPIOS-1:0] prv_${module_instance_name}_i_pins_oe;
  // Flag to store value to be updated for INTR_STATE register
  // and to indicate whether value change is due currently
  ${module_instance_name}_reg_update_due_t intr_state_update_queue[$];
  // data_in update queue
  ${module_instance_name}_reg_update_due_t data_in_update_queue[$];
  // Latest Interrupt state update due to either of following reasons:
  //  (i) ${module_instance_name} value change
  // (ii) interrupt control register value(s) write
  // This flag is not meant for update when intr_state register is written
  bit [TL_DW-1:0] last_intr_update_except_clearing;
  // Value seen in last Interrupt Test write
  bit [TL_DW-1:0] last_intr_test_event;
  // Flag to:
  //  (i) indicate that write to INTR_STATE register just happened, and
  // (ii) store information of which all interupt bits were cleared
  bit [TL_DW-1:0] cleared_intr_bits;
  // Flag to indicate that the strap was triggered
  bit first_strap_triggered;

  // mask are WO, store the values in scb
  uvm_reg_data_t masked_out_lower_mask;
  uvm_reg_data_t masked_out_upper_mask;

  string common_seq_type;

  // Used to get the ${module_instance_name} data inputs/outputs from the monitor.
  uvm_analysis_imp #(${module_instance_name}_seq_item, ${module_instance_name}_scoreboard) analysis_port;

  `uvm_component_utils(${module_instance_name}_scoreboard)

  function new (string name = "${module_instance_name}_scoreboard", uvm_component parent = null);
    super.new (name, parent);
  endfunction

  // Function: build_phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_port = new("analysis_port", this);
  endfunction

  // Task: run_phase
  task run_phase(uvm_phase phase);
    void'($value$plusargs("run_%0s", common_seq_type));
    super.run_phase(phase);
    fork
      monitor_${module_instance_name}_i();
      monitor_${module_instance_name}_interrupt_pins();
    join_none
  endtask

  // Task: write function to get the ${module_instance_name}_seq_item from the straps monitor
  // and call the checker function.
  virtual function void write(${module_instance_name}_seq_item item);

    // Update the predicted value for strap registers.
    update_${module_instance_name}_straps_regs(item);

    // Check if the ${module_instance_name}_i input data is matching with the strap output data.
    check_straps_data(item);

  endfunction : write

  virtual function void update_${module_instance_name}_straps_regs(${module_instance_name}_seq_item item);
    // Update data_in ral register value based on result of input
    if(!cfg.clk_rst_vif.rst_n) begin
      // Update data_in valid register value based on result of input
      `DV_CHECK_FATAL(ral.hw_straps_data_in_valid.predict(.value('b0),
                                                          .kind(UVM_PREDICT_DIRECT)));
      `DV_CHECK_FATAL(ral.hw_straps_data_in.predict(.value(0),
                                                  .kind(UVM_PREDICT_DIRECT)));
    end else begin
      if(item.strap_en_i) begin
        // Update data_in valid register value based on result of input
        `DV_CHECK_FATAL(ral.hw_straps_data_in_valid.predict(.value('b1),
                                                            .kind(UVM_PREDICT_DIRECT)));
        `DV_CHECK_FATAL(ral.hw_straps_data_in.predict(.value(item.cio_gpio_i),
                                                    .kind(UVM_PREDICT_DIRECT)));
      end else begin
        // Update data_in valid register value based on result of input
        `DV_CHECK_FATAL(ral.hw_straps_data_in_valid.predict(.value('b0),
                                                            .kind(UVM_PREDICT_DIRECT)));
        `DV_CHECK_FATAL(ral.hw_straps_data_in.predict(.value('b0),
                                                    .kind(UVM_PREDICT_DIRECT)));
      end
    end
  endfunction : update_${module_instance_name}_straps_regs

  // Task: check_straps_data
  // Check the sampled straps data
  virtual function void check_straps_data(${module_instance_name}_seq_item item);
    // Check the sampled straps data
    `uvm_info(`gfn, "Checking the sampled straps data", UVM_HIGH)
    if(cfg.clk_rst_vif.rst_n) begin
      if(item.strap_en_i) begin
        // Checker: Compare actual values of ${module_instance_name} pins with straps register.
        // Check the register hw_straps_data_in against ${module_instance_name}_i pins
        `DV_CHECK_CASE_EQ(item.cio_gpio_i, item.sampled_straps_o.data)
        // Check the register hw_straps_data_in_valid
        `DV_CHECK_CASE_EQ(1, item.sampled_straps_o.valid)
      end else begin
        // Checker: Compare actual values of ${module_instance_name} pins with straps register.
        // Check the register hw_straps_data_in against ${module_instance_name}_i pins
        `DV_CHECK_CASE_EQ(0, item.sampled_straps_o.data)
        // Check the register hw_straps_data_in_valid
        `DV_CHECK_CASE_EQ(0, item.sampled_straps_o.valid)
      end
    end

  endfunction : check_straps_data

  // Task : process_tl_access
  // process monitored tl transaction
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit do_read_check       = 1'b1;
    bit write               = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // grab completed transactions from data channel; ignore packets from address channel
    if (channel == AddrChannel) begin
      // Clock period in nano seconds (timeunit)
      real clk_period = cfg.clk_rst_vif.clk_period_ps / 1000;
      time crnt_time = $time;

      // apply pending update for `data_in` register
      if (data_in_update_queue.size() > 0) begin
        if (data_in_update_queue[$].needs_update == 1'b1 &&
            (int'((crnt_time - data_in_update_queue[$].eval_time) / clk_period)) > 1) begin
          void'(ral.data_in.predict(.value(data_in_update_queue[$].reg_value),
                                    .kind(UVM_PREDICT_READ)));
        end else if(data_in_update_queue[$ - 1].needs_update == 1'b1) begin
          // Use previous updated value for "data_in" prediction
          void'(ral.data_in.predict(.value(data_in_update_queue[$ - 1].reg_value),
              .kind(UVM_PREDICT_READ)));
        end
      end

      // apply pending update for interrupt state
      if (intr_state_update_queue.size() > 0) begin
        // As register read takes single clock cycle to latch the updated value, immediate
        // read on same or next clock will not give latest updated value. So, look for time stamp
        // of latest update to decide which value to predict for "intr_state" mirrored value
        if (intr_state_update_queue[$].needs_update == 1'b1 &&
            (int'((crnt_time - intr_state_update_queue[$].eval_time) / clk_period)) > 1) begin
          void'(ral.intr_state.predict(.value(intr_state_update_queue[$].reg_value),
              .kind(UVM_PREDICT_READ)));
        end else if(intr_state_update_queue[$ - 1].needs_update == 1'b1) begin
          // Use previous updated value for "intr_state" prediction
          void'(ral.intr_state.predict(.value(intr_state_update_queue[$ - 1].reg_value),
              .kind(UVM_PREDICT_READ)));
        end
      end

      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        // GPIO scoreboard is cycle accurate and will only update `intr_state` mirrored value at
        // the address phase of the next read operation.
        // This is too late for intr_test and intr_test does not need this cycle accurate model,
        // So we use csr predict function right after the write operations.
        if ((common_seq_type == "intr_test") &&
            (csr.get_name() inside {"intr_state", "intr_enable", "intr_test"})) begin
          void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        end
        if (csr.get_name() == "intr_state") begin
          // As per rtl definition of W1C, hardware must get a chance to make update
          // to interrupt state first, so we need to clear interrupt only after possible
          // interrupt update due to ${module_instance_name} change
          #0;
          `uvm_info(`gfn, $sformatf("Write on intr_state: write data = %0h", item.a_data), UVM_HIGH)
          if (intr_state_update_queue.size() > 0) begin
            ${module_instance_name}_reg_update_due_t intr_state_write_to_clear_update = intr_state_update_queue[$];
            `uvm_info(`gfn, $sformatf("Entry taken out for clearing is %0p",
                intr_state_write_to_clear_update), UVM_HIGH)
            // Update time
            intr_state_write_to_clear_update.eval_time = $time;
            for (uint each_bit = 0; each_bit < TL_DW; each_bit++) begin
              if (intr_state_write_to_clear_update.needs_update == 1'b1 &&
                  intr_state_write_to_clear_update.reg_value[each_bit] == 1'b1 &&
                  item.a_data[each_bit] == 1'b1) begin
                intr_state_write_to_clear_update.reg_value[each_bit] = 1'b0;
                cleared_intr_bits[each_bit] = 1'b1;
                // Coverage Sampling: ${module_instance_name} interrupt cleared
                if (cfg.en_cov) begin
                  cov.intr_state_cov_obj[each_bit].sample(1'b0);
                end
              end
            end
            // If same time stamp as last entry, update entry to account for "still active" event
            // that caused last interrupt update (As per definition of w1c in comportability
            // specification)
            if (intr_state_write_to_clear_update.eval_time == intr_state_update_queue[$].eval_time)
            begin
              // Re-apply interrupt update
              intr_state_write_to_clear_update.reg_value |= last_intr_update_except_clearing;
              // Delete last entry with same time stamp
              intr_state_update_queue.delete(intr_state_update_queue.size()-1);
              // Coverage Sampling: cover a scenario wherein cleared interrupt state bit
              // is re-asserted due to still active interrupt event
              // Note: In this case, both interrupt clearing event and INTR_STATE reg write
              // have occurred at the same time.
              if (cfg.en_cov) begin
                foreach (cleared_intr_bits[each_bit]) begin
                  if (cleared_intr_bits[each_bit]) begin
                    if (last_intr_update_except_clearing[each_bit]) begin
                      cov.sticky_intr_cov[{"${module_instance_name}_sticky_intr_pin",
                          $sformatf("%0d", each_bit)}].sample(1'b1);
                    end else begin
                      cov.sticky_intr_cov[{"${module_instance_name}_sticky_intr_pin",
                          $sformatf("%0d", each_bit)}].sample(1'b0);
                    end
                  end
                end
              end
            end
            // Push new interrupt state update entry into queue
            intr_state_update_queue.push_back(intr_state_write_to_clear_update);
            if (intr_state_update_queue.size() > 2) begin
              // Delete extra unnecessary entry
              intr_state_update_queue.delete(0);
            end
          end
        end else begin
          if (csr.get_name() == "intr_test") begin
            // Store the written value as it is WO register
            last_intr_test_event = item.a_data;
          end else begin
            // Coverage Sampling: coverage on *out* and *oe* register values
            if (cfg.en_cov && (!uvm_re_match("*out*", csr.get_name()) ||
                  !uvm_re_match("*oe*", csr.get_name()))) begin
              for (uint each_pin = 0; each_pin < NUM_GPIOS; each_pin++) begin
                cov.out_oe_cov_objs[each_pin][csr.get_name()].sample(item.a_data[each_pin]);
              end
              // Coverage Sampling: Cross coverage on mask and data within masked_* registers
              if (!uvm_re_match("masked*", csr.get_name())) begin
                bit [(NUM_GPIOS/2) - 1:0] mask, data;
                {mask, data} = item.a_data;
                for (uint each_pin = 0; each_pin < NUM_GPIOS/2; each_pin++) begin
                  cov.out_oe_mask_data_cov_objs[each_pin][csr.get_name()].var1_var2_cg.sample(
                    mask[each_pin], data[each_pin]);
                end
              end
            end
            // these fields are WO, save values in scb
            if (csr.get_name() == "masked_out_lower") begin
              masked_out_lower_mask = get_field_val(ral.masked_out_lower.mask, item.a_data);
            end else if (csr.get_name() == "masked_out_upper") begin
              masked_out_upper_mask = get_field_val(ral.masked_out_upper.mask, item.a_data);
            end
            void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
          end
        end
        `uvm_info(`gfn, "Calling ${module_instance_name}_predict_and_compare on reg write", UVM_HIGH)
        ${module_instance_name}_predict_and_compare(csr);
      end // if (write)
    end else begin // if (channel == DataChannel)
      if (write == 0) begin
        `uvm_info(`gfn, $sformatf("csr read on %0s", csr.get_name()), UVM_HIGH)
        // If do_read_check, is set, then check mirrored_value against item.d_data
        if (do_read_check) begin
          // Checker-2: Check if reg read data matches expected value or not
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
          // Checker-3: Check value of interrupt pins against predicted value
          if (csr.get_name() == "intr_state") begin
            bit [TL_DW-1:0] intr_state = (intr_state_update_queue.size() > 0) ?
                                          intr_state_update_queue[$].reg_value :
                                          csr.get_mirrored_value();
            bit [TL_DW-1:0] pred_val_intr_pins = intr_state &
                                                ral.intr_enable.get_mirrored_value();
            // according to issue #841, interrupt is a flop and the value will be updated after one
            // clock cycle. Because the `pred_val_intr_pins` might be updated during the one clk
            // cycle, we store the predicted intr val into a temp automatic variable.
            fork
              begin
                automatic bit [TL_DW-1:0] pred_val_intr_pins_temp = pred_val_intr_pins;
                cfg.clk_rst_vif.wait_clks(1);
                if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.pins, pred_val_intr_pins_temp)
              end
            join_none
          end
        end
      end // if (write == 0)
    end
  endtask : process_tl_access

  // Task : monitor_${module_instance_name}_i
  // monitor ${module_instance_name} input pins interface
  virtual task monitor_${module_instance_name}_i();

    logic [NUM_GPIOS-1:0] prev_${module_instance_name}_i;
    prev_${module_instance_name}_i = cfg.${module_instance_name}_vif.pins;

    forever begin : monitor_pins_if
      @(cfg.${module_instance_name}_vif.pins or cfg.under_reset);
      `uvm_info(`gfn, $sformatf("cfg.${module_instance_name}_vif.pins = %0h, under_reset = %0b",
                                cfg.${module_instance_name}_vif.pins, cfg.under_reset), UVM_HIGH)
      if (cfg.under_reset == 1'b0) begin
        // Coverage Sampling: ${module_instance_name} pin values' coverage
        if (cfg.en_cov) begin
          foreach (cov.${module_instance_name}_pin_values_cov_obj[each_pin]) begin
            cov.${module_instance_name}_pin_values_cov_obj[each_pin].sample(cfg.${module_instance_name}_vif.pins[each_pin]);
          end
        end
        // evaluate ${module_instance_name} input driven to dut
        foreach (cfg.${module_instance_name}_vif.pins_oe[pin_num]) begin
          if (cfg.${module_instance_name}_vif.pins_oe[pin_num] == 1'b1) begin
            ${module_instance_name}_i_driven[pin_num] = cfg.${module_instance_name}_vif.pins_o[pin_num];
          end else begin
            ${module_instance_name}_i_driven[pin_num] = 1'bz;
          end
          `uvm_info(`gfn, $sformatf("pins_oe[%0d] = %0b pins_o[%0d] = %0b ${module_instance_name}_i_driven[%0d] = %0b",
              pin_num, cfg.${module_instance_name}_vif.pins_oe[pin_num], pin_num,
              cfg.${module_instance_name}_vif.pins_o[pin_num], pin_num, ${module_instance_name}_i_driven[pin_num]),
            UVM_HIGH)
        end

        `uvm_info(`gfn, $sformatf("pins = 0x%0h [%0b]) ${module_instance_name}_i_driven = 0x%0h [%0b]",
            cfg.${module_instance_name}_vif.pins, cfg.${module_instance_name}_vif.pins, ${module_instance_name}_i_driven,
            ${module_instance_name}_i_driven), UVM_HIGH)
        // Predict effect on ${module_instance_name} pins
        ${module_instance_name}_predict_and_compare();

        if (prev_${module_instance_name}_i !== cfg.${module_instance_name}_vif.pins) begin
          // Flag to indicate:
          // (i) if there was any change in value on ${module_instance_name}_i pin - Bit0
          // (ii) what change occurred on ${module_instance_name}_i pin - Bit1
          ${module_instance_name}_transition_t [NUM_GPIOS-1:0] ${module_instance_name}_i_transition;
          foreach (prev_${module_instance_name}_i[pin]) begin
            ${module_instance_name}_i_transition[pin].transition_occurred =
              (cfg.${module_instance_name}_vif.pins[pin] !== prev_${module_instance_name}_i[pin]);
            if (${module_instance_name}_i_transition[pin].transition_occurred) begin
              case (cfg.${module_instance_name}_vif.pins[pin])
                1'b0: begin
                  // Negedge seen on pin, indicated by 0 value
                  ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b0;
                end
                1'b1: begin
                  // Posedge seen on pin, indicated by 1 value
                  ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b1;
                end
                1'bz: begin
                  if (prev_${module_instance_name}_i[pin] === 1'b1) begin
                    // Negedge seen on pin, indicated by 0 value
                    ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b0;
                  end else if (prev_${module_instance_name}_i[pin] === 1'b0) begin
                    // Posedge seen on pin, indicated by 1 value
                    ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b1;
                  end else begin
                    // x->z does not indicate useful transition, reset transition bit
                    ${module_instance_name}_i_transition[pin].transition_occurred = 1'b0;
                  end
                end
                1'bx: begin
                  if (prev_${module_instance_name}_i[pin] === 1'b1) begin
                    // Negedge seen on pin, indicated by 0 value
                    ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b0;
                  end else if (prev_${module_instance_name}_i[pin] === 1'b0) begin
                    // Posedge seen on pin, indicated by 1 value
                    ${module_instance_name}_i_transition[pin].is_rising_edge = 1'b1;
                  end else begin
                    // z->x does not indicate useful transition, reset transition bit
                    ${module_instance_name}_i_transition[pin].transition_occurred = 1'b0;
                  end
                end
                default: begin
                  `uvm_info(`gfn, "${module_instance_name} pin undefined!", UVM_HIGH)
                end
              endcase
            end
          end
          foreach (${module_instance_name}_i_transition[ii]) begin
            `uvm_info(`gfn, $sformatf("${module_instance_name}_i_transition[%0d] = %0p", ii, ${module_instance_name}_i_transition[ii]),
              UVM_HIGH)
          end
          `uvm_info(`gfn, "Calling ${module_instance_name}_interrupt_predict from monitor_pins_if", UVM_HIGH)
          // Look for interrupt event and update interrupt status
          ${module_instance_name}_interrupt_predict(${module_instance_name}_i_transition);
          // Update value
          prev_${module_instance_name}_i = cfg.${module_instance_name}_vif.pins;
          `uvm_info(`gfn, $sformatf("updated prev_${module_instance_name}_i = 0x%0h [%0b]", prev_${module_instance_name}_i, prev_${module_instance_name}_i),
            UVM_HIGH)
        end
        // Update "previous pins if out and out enable" values
        prv_${module_instance_name}_i_pins_o = cfg.${module_instance_name}_vif.pins_o;
        prv_${module_instance_name}_i_pins_oe = cfg.${module_instance_name}_vif.pins_oe;
        `uvm_info(`gfn, $sformatf("prv_${module_instance_name}_i_pins_o = 0x%0h [%0b]",
            prv_${module_instance_name}_i_pins_o, prv_${module_instance_name}_i_pins_o), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("prv_${module_instance_name}_i_pins_oe = 0x%0h [%0b]",
            prv_${module_instance_name}_i_pins_oe, prv_${module_instance_name}_i_pins_oe), UVM_HIGH)
      end
    end // monitor_pins_if
  endtask : monitor_${module_instance_name}_i

  // Task: monitor_${module_instance_name}_interrupt_pins
  virtual task monitor_${module_instance_name}_interrupt_pins();
    forever begin : monitor_${module_instance_name}_intr
      @(cfg.intr_vif.pins or cfg.under_reset) begin
        if (cfg.under_reset == 0) begin
          if (cfg.en_cov) begin
            // Coverage Sampling: ${module_instance_name} interrupt pin values and transitions
            for (uint each_pin = 0; each_pin < NUM_GPIOS; each_pin++) begin
              cov.intr_pins_cg.sample(each_pin, cfg.intr_vif.pins[each_pin]);
            end
          end
        end
      end
    end
  endtask : monitor_${module_instance_name}_interrupt_pins

  // Function: actual_${module_instance_name}_i_activity
  function bit actual_${module_instance_name}_i_activity();
    return ~((prv_${module_instance_name}_i_pins_o === cfg.${module_instance_name}_vif.pins_o) &&
      (prv_${module_instance_name}_i_pins_oe === cfg.${module_instance_name}_vif.pins_oe));
  endfunction : actual_${module_instance_name}_i_activity

  // Function : ${module_instance_name}_predict_and_compare
  function void ${module_instance_name}_predict_and_compare(uvm_reg csr = null);
    string msg_id = {`gfn, " ${module_instance_name}_predict_and_compare: "};
    // Predicted value of "pins" from within ${module_instance_name}_vif
    logic [NUM_GPIOS-1:0] pred_val_${module_instance_name}_pins;
    // Flag to decide if ${module_instance_name} data prediction and check are required
    bit ${module_instance_name}_data_check = 1'b1;

    if (csr != null) begin
      // process the csr req
      case (csr.get_name())
        "data_in": begin
          ${module_instance_name}_data_check = 1'b0;
        end
        "direct_out": begin
          data_out = csr.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
            UVM_HIGH)
          // Update mirror values of *out* registers
          update_${module_instance_name}_out_regs();
        end
        "masked_out_lower": begin
          uvm_reg_data_t data = ral.masked_out_lower.data.get_mirrored_value();

          for (uint pin_idx = 0;
              pin_idx < ral.masked_out_lower.mask.get_n_bits(); pin_idx++) begin
            if (masked_out_lower_mask[pin_idx] == 1'b1) begin
              data_out[pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
            UVM_HIGH)
          // Update mirror values of *out* registers
          update_${module_instance_name}_out_regs();
        end
        "masked_out_upper": begin
          uvm_reg_data_t data = ral.masked_out_upper.data.get_mirrored_value();

          for (uint pin_idx = 0; pin_idx < ral.masked_out_upper.mask.get_n_bits(); pin_idx++) begin
            if (masked_out_upper_mask[pin_idx] == 1'b1) begin
              data_out[(NUM_GPIOS / 2) + pin_idx] = data[pin_idx];
            end
          end
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
            UVM_HIGH)
          // Update mirror values of *out* registers
          update_${module_instance_name}_out_regs();
        end
        "direct_oe": begin
          data_oe = csr.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("data_out updated to 0x%0h [%0b]", data_out, data_out),
            UVM_HIGH)
          // Update mirror values of *oe* registers
          update_${module_instance_name}_oe_regs();
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
          update_${module_instance_name}_oe_regs();
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
          update_${module_instance_name}_oe_regs();
        end
        "intr_enable": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_state": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_test": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_ctrl_en_rising": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_ctrl_en_falling": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_ctrl_en_lvlhigh": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "intr_ctrl_en_lvllow": begin
          ${module_instance_name}_data_check = 1'b0;
          ${module_instance_name}_interrupt_predict();
        end
        "ctrl_en_input_filter": begin
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    // GPIO inout signal value check
    if (${module_instance_name}_data_check == 1'b1) begin
      // effect of ${module_instance_name}_o on ${module_instance_name}_i based on ${module_instance_name}_oe
      logic [NUM_GPIOS-1:0] data_out_effect_on_${module_instance_name}_i;
      // As there is a common net that drives ${module_instance_name}_i and gets driven through ${module_instance_name}_o
      // based on ${module_instance_name}_oe, ${module_instance_name}_i will have effect of (${module_instance_name}_o & ${module_instance_name}_oe) value
      foreach (data_oe[pin_num]) begin
        if (data_oe[pin_num] === 1'b1) begin
          data_out_effect_on_${module_instance_name}_i[pin_num] = data_out[pin_num];
        end else begin
          data_out_effect_on_${module_instance_name}_i[pin_num] = 1'bz;
        end
      end
      `uvm_info(msg_id, $sformatf("data_out_effect_on_${module_instance_name}_i = 0x%0h [%0b]",
          data_out_effect_on_${module_instance_name}_i, data_out_effect_on_${module_instance_name}_i), UVM_HIGH)
      `uvm_info(msg_id, $sformatf("${module_instance_name}_i_driven = 0x%0h [%0b]", ${module_instance_name}_i_driven, ${module_instance_name}_i_driven),
        UVM_HIGH)

      // Predict effective value of common wire that-
      // (i) drives ${module_instance_name}_i, and
      // (ii) gets driven by ${module_instance_name}_o based on ${module_instance_name}oe value
      for (uint pin_num = 0; pin_num < NUM_GPIOS; pin_num++) begin
        if (data_out_effect_on_${module_instance_name}_i[pin_num] === 1'bz) begin
          pred_val_${module_instance_name}_pins[pin_num] = ${module_instance_name}_i_driven[pin_num];
        end else if (${module_instance_name}_i_driven[pin_num] === 1'bz) begin
          pred_val_${module_instance_name}_pins[pin_num] = data_out_effect_on_${module_instance_name}_i[pin_num];
        end else if (data_out_effect_on_${module_instance_name}_i[pin_num] === ${module_instance_name}_i_driven[pin_num]) begin
          pred_val_${module_instance_name}_pins[pin_num] = data_out_effect_on_${module_instance_name}_i[pin_num];
        end else begin
          pred_val_${module_instance_name}_pins[pin_num] = 1'bx;
        end
        if (pred_val_${module_instance_name}_pins[pin_num] === 1'bz) begin
          if (cfg.${module_instance_name}_vif.pins_pu[pin_num] == 1'b1) begin
            pred_val_${module_instance_name}_pins[pin_num] = 1'b1;
          end else if (cfg.${module_instance_name}_vif.pins_pd[pin_num] == 1'b1) begin
            pred_val_${module_instance_name}_pins[pin_num] = 1'b0;
          end
        end
      end
      `uvm_info(msg_id, $sformatf("pred_val_${module_instance_name}_pins = %0h(%0b)", pred_val_${module_instance_name}_pins,
          pred_val_${module_instance_name}_pins), UVM_HIGH)

      // Store latest update to be applied to data_in
      begin
        ${module_instance_name}_reg_update_due_t current_data_in_update;
        if (data_in_update_queue.size == 2) begin
          data_in_update_queue.delete(0);
        end
        current_data_in_update.needs_update = 1'b1;
        current_data_in_update.reg_value = pred_val_${module_instance_name}_pins;
        current_data_in_update.eval_time = $time;
        data_in_update_queue.push_back(current_data_in_update);
        // Coverage Sampling: data_in register coverage
        // Coverage Sampling: Cross coverage between data_out, data_oe and data_in
        // values per bit
        if (cfg.en_cov) begin
          for (uint each_bit = 0; each_bit < NUM_GPIOS; each_bit++) begin
            cov.data_in_cov_obj[each_bit].sample(pred_val_${module_instance_name}_pins[each_bit]);
            cov.data_out_data_oe_data_in_cross_cg.sample(each_bit, data_out[each_bit],
              data_oe[each_bit], pred_val_${module_instance_name}_pins[each_bit]);
            cov.${module_instance_name}_pins_data_in_cross_cg.sample(each_bit, cfg.${module_instance_name}_vif.pins[each_bit],
              pred_val_${module_instance_name}_pins[each_bit]);
          end
        end
      end
      // If update was due to register write, we can call predict right away
      if (csr != null) begin
        // Update data_in register value based on result of input and output
        void'(ral.data_in.data_in.predict(.value(pred_val_${module_instance_name}_pins), .kind(UVM_PREDICT_DIRECT)));
      end

      // Checker-1: Compare predicted and actual values of ${module_instance_name} pins
      // Avoid calling this checker due to weak pull-up or pull-down effect
      if ((csr != null) ||
          ((|${module_instance_name}_i_driven === 1'b1) && (actual_${module_instance_name}_i_activity() == 1))) begin
        `DV_CHECK_CASE_EQ(pred_val_${module_instance_name}_pins, cfg.${module_instance_name}_vif.pins)
      end

    end

  endfunction : ${module_instance_name}_predict_and_compare

  // Function : ${module_instance_name}_interrupt_predict
  // This function computes expected value of ${module_instance_name} intr_status based on
  // changes of ${module_instance_name}_i data or interrupt control registers
  virtual function void ${module_instance_name}_interrupt_predict(
      input ${module_instance_name}_transition_t [NUM_GPIOS-1:0] ${module_instance_name}_i_transition = {NUM_GPIOS{2'b00}});

    string msg_id = {`gfn, $sformatf(" ${module_instance_name}_interrupt_predict: ")};
    bit [TL_DW-1:0] intr_enable          = ral.intr_enable.get_mirrored_value();
    bit [TL_DW-1:0] intr_state           = ral.intr_state.get_mirrored_value();
    bit [TL_DW-1:0] intr_ctrl_en_rising  = ral.intr_ctrl_en_rising.get_mirrored_value();
    bit [TL_DW-1:0] intr_ctrl_en_falling = ral.intr_ctrl_en_falling.get_mirrored_value();
    bit [TL_DW-1:0] intr_ctrl_en_lvlhigh = ral.intr_ctrl_en_lvlhigh.get_mirrored_value();
    bit [TL_DW-1:0] intr_ctrl_en_lvllow  = ral.intr_ctrl_en_lvllow.get_mirrored_value();
    // expected(predicted) value of interrupt status
    bit [TL_DW-1:0] exp_intr_status;

    // Reset value of last_intr_update_except_clearing to 0
    last_intr_update_except_clearing = '0;
    // Check if there is already INTR_STATE value update which was already due
    // for update, but not actually updated
    if (intr_state_update_queue.size() > 0) begin
      if (intr_state_update_queue[$].needs_update) begin
        intr_state = intr_state_update_queue[$].reg_value;
      end
    end

    // Coverage Sampling: ${module_instance_name} interrupt types
    if (cfg.en_cov) begin
      foreach (intr_ctrl_en_rising[each_bit]) begin
        cov.intr_ctrl_en_cov_objs[each_bit]["intr_ctrl_en_rising"].sample(
          intr_ctrl_en_rising[each_bit]);
        cov.intr_ctrl_en_cov_objs[each_bit]["intr_ctrl_en_falling"].sample(
          intr_ctrl_en_falling[each_bit]);
        cov.intr_ctrl_en_cov_objs[each_bit]["intr_ctrl_en_lvlhigh"].sample(
          intr_ctrl_en_lvlhigh[each_bit]);
        cov.intr_ctrl_en_cov_objs[each_bit]["intr_ctrl_en_lvllow"].sample(
          intr_ctrl_en_lvllow[each_bit]);
      end
    end
    // 1. Look for edge triggerred interrupts
    begin
      bit [TL_DW-1:0] rising_edge_intr_events, falling_edge_intr_events;
      if (${module_instance_name}_i_transition != {NUM_GPIOS{2'b00}}) begin
        foreach (rising_edge_intr_events[each_bit]) begin
          if (${module_instance_name}_i_transition[each_bit].transition_occurred) begin
            rising_edge_intr_events[each_bit]  = ${module_instance_name}_i_transition[each_bit].is_rising_edge &
              intr_ctrl_en_rising[each_bit];
            falling_edge_intr_events[each_bit] = !${module_instance_name}_i_transition[each_bit].is_rising_edge &
              intr_ctrl_en_falling[each_bit];
          end
        end
        foreach (${module_instance_name}_i_transition[each_bit]) begin
          if (${module_instance_name}_i_transition[each_bit].transition_occurred) begin
            if (rising_edge_intr_events[each_bit] || falling_edge_intr_events[each_bit]) begin
              exp_intr_status[each_bit] = 1'b1;
              // Register the latest edge triggered ${module_instance_name} interrupt update, if any
              last_intr_update_except_clearing[each_bit] = 1'b1;
            end else begin
              exp_intr_status[each_bit] = intr_state[each_bit];
            end
          end
        end
      end
      // Coverage Sampling: Cross coverage of (edge tiggered intr type)x(enable)x(state)
      // when type is enabled
      if (cfg.en_cov) begin
        foreach (rising_edge_intr_events[each_bit]) begin
          cov.intr_event_type_cov_objs[each_bit]["intr_event_rising"].intr_type_cg.sample(
            intr_ctrl_en_rising[each_bit],
            intr_enable[each_bit],
            rising_edge_intr_events[each_bit]);
          cov.intr_event_type_cov_objs[each_bit]["intr_event_falling"].intr_type_cg.sample(
            intr_ctrl_en_falling[each_bit],
            intr_enable[each_bit],
            falling_edge_intr_events[each_bit]);
        end
      end
    end
    // 2. Look for level triggerred interrupts
    begin
      bit [TL_DW-1:0] lvlhigh_intr_events, lvllow_intr_events;
      for (uint each_bit = 0; each_bit < TL_DW; each_bit++) begin
        lvlhigh_intr_events[each_bit] = (cfg.${module_instance_name}_vif.pins[each_bit] == 1'b1) &&
          (intr_ctrl_en_lvlhigh[each_bit] == 1'b1);
        lvllow_intr_events[each_bit]  = (cfg.${module_instance_name}_vif.pins[each_bit] == 1'b0) &&
          (intr_ctrl_en_lvllow[each_bit] == 1'b1);
        if (exp_intr_status[each_bit] == 1'b0) begin
          if (lvlhigh_intr_events[each_bit] || lvllow_intr_events[each_bit]) begin
            exp_intr_status[each_bit] = 1'b1;
            // Register the latest level triggered ${module_instance_name} interrupt update, if any
            last_intr_update_except_clearing[each_bit] = 1'b1;
          end else begin
            exp_intr_status[each_bit] = intr_state[each_bit];
          end
        end
      end
      // Coverage Sampling: Cross coverage of (edge tiggered intr type)x(enable)x(state)
      // when type is enabled
      if (cfg.en_cov) begin
        foreach (lvlhigh_intr_events[each_bit]) begin
          cov.intr_event_type_cov_objs[each_bit]["intr_event_lvlhigh"].intr_type_cg.sample(
            intr_ctrl_en_lvlhigh[each_bit],
            intr_enable[each_bit],
            lvlhigh_intr_events[each_bit]);
          cov.intr_event_type_cov_objs[each_bit]["intr_event_lvllow"].intr_type_cg.sample(
            intr_ctrl_en_lvllow[each_bit],
            intr_enable[each_bit],
            lvllow_intr_events[each_bit]);
        end
      end
    end
    // 3. Apply effect of "Interrupt Test"
    exp_intr_status |= last_intr_test_event;
    `uvm_info(`gfn, $sformatf("updated intr_state is %0h", exp_intr_status), UVM_HIGH)
    // Coverage Sampling: Coverage on Interrupt Index, Interrupt Enable,
    // Interrupt Status and their cross coverage
    if (cfg.en_cov) begin
      foreach (exp_intr_status[each_bit]) begin
        cov.intr_cg.sample(each_bit, intr_enable[each_bit], exp_intr_status[each_bit]);
        cov.intr_state_cov_obj[each_bit].sample(last_intr_update_except_clearing[each_bit]);
        // Coverage Sampling: cover a scenario wherein cleared interrupt state bit
        // is re-asserted due to still active interrupt event
        if (cleared_intr_bits[each_bit]) begin
          if (exp_intr_status[each_bit]) begin
            cov.sticky_intr_cov[{"${module_instance_name}_sticky_intr_pin", $sformatf("%0d", each_bit)}].sample(1'b1);
          end else begin
            cov.sticky_intr_cov[{"${module_instance_name}_sticky_intr_pin", $sformatf("%0d", each_bit)}].sample(1'b0);
          end
          // Clear the flag
          cleared_intr_bits[each_bit] = 1'b0;
        end
        // Interrupt Test coverage
        cov.intr_test_cg.sample(each_bit,
          last_intr_test_event[each_bit],
          intr_enable[each_bit],
          exp_intr_status[each_bit]);
      end
    end
    // Clear last_intr_test_event
    last_intr_test_event = '0;
    `uvm_info(msg_id, $sformatf("Predicted interrupt status = 0x%0h [%0b]",
        exp_intr_status, exp_intr_status), UVM_HIGH)
    begin
      ${module_instance_name}_reg_update_due_t crnt_intr_state_update;
      // Keep update pending until register access is done
      crnt_intr_state_update.needs_update = 1'b1;
      crnt_intr_state_update.reg_value = exp_intr_status;
      crnt_intr_state_update.eval_time = $time;
      // Push new entry into queue
      intr_state_update_queue.push_back(crnt_intr_state_update);

      // If queue already has two entries, remove 0th element
      if (intr_state_update_queue.size() > 2) begin
        intr_state_update_queue.delete(0);
      end
    end
  endfunction : ${module_instance_name}_interrupt_predict

  // Function : update_${module_instance_name}_out_regs
  // This function is used for updating direct_out, masked_out_upper and masked_out_lower
  // register values based on write to any one of these 3 registers.
  // Note : Assumption for this method is that data_out has already been updated
  //        before calling the method.
  function void update_${module_instance_name}_out_regs();
    uvm_reg_data_t data;
    // 1. Update "direct_out" register for writes to masked_out_* registers
    //    For write to "direct_out", it must have been updated already.
    void'(ral.direct_out.predict(.value(data_out), .kind(UVM_PREDICT_WRITE)));
    // 2. Update masked_out_lower
    data = data_out;
    for (uint idx = ral.masked_out_lower.data.get_n_bits();
        idx < `UVM_REG_DATA_WIDTH;
        idx++) begin
      data[idx] = 1'b0;
    end
    void'(ral.masked_out_lower.data.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    // 3. Update masked_out_upper
    data = 0;
    for (uint idx = ral.masked_out_upper.data.get_n_bits();
        idx < `UVM_REG_DATA_WIDTH;
        idx++) begin
      data[idx - ral.masked_out_upper.data.get_n_bits()] = data_out[idx];
    end
    void'(ral.masked_out_upper.data.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    // Coverage Sampling: Coverage on DATA_OUT values and its combinations with DATA_OE
    sample_data_out_data_oe_coverage();
  endfunction : update_${module_instance_name}_out_regs

  // Function : update_${module_instance_name}_oe_regs
  // This function is used for updating direct_oe, masked_oe_upper and masked_oe_lower
  // register values based on write to any one of these 3 registers.
  // Note : Assumption for this method is that data_oe has already been updated
  //        before calling the method.
  function void update_${module_instance_name}_oe_regs();
    uvm_reg_data_t data;
    const uvm_reg_data_t mask = 0;
    // 1. Update "direct_oe" register for writes to masked_oe_* registers
    //    For write to "direct_oe", it must have been updated already.
    void'(ral.direct_oe.predict(.value(data_oe), .kind(UVM_PREDICT_WRITE)));
    // 2. Update masked_oe_lower
    data = data_oe;
    for (uint idx = ral.masked_oe_lower.data.get_n_bits(); idx < `UVM_REG_DATA_WIDTH; idx++) begin
      data[idx] = 1'b0;
    end
    void'(ral.masked_oe_lower.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE)));
    void'(ral.masked_oe_lower.data.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    // 3. Update masked_oe_upper
    data = 0;
    for (uint idx = ral.masked_oe_upper.data.get_n_bits(); idx < `UVM_REG_DATA_WIDTH; idx++) begin
      data[idx - ral.masked_oe_upper.data.get_n_bits()] = data_oe[idx];
    end
    void'(ral.masked_oe_upper.mask.predict(.value(mask), .kind(UVM_PREDICT_WRITE)));
    void'(ral.masked_oe_upper.data.predict(.value(data), .kind(UVM_PREDICT_WRITE)));
    // Coverage Sampling: Coverage on DATA_OUT values and its combinations with DATA_OE
    sample_data_out_data_oe_coverage();
  endfunction : update_${module_instance_name}_oe_regs

  // Function: sample_data_out_data_oe_coverage
  function void sample_data_out_data_oe_coverage();
    if (cfg.en_cov) begin
      for (uint each_bit = 0; each_bit < NUM_GPIOS; each_bit++) begin
        cov.data_out_data_oe_cov_obj[each_bit].var1_var2_cg.sample(data_out[each_bit],
          data_oe[each_bit]);
      end
    end
  endfunction : sample_data_out_data_oe_coverage

  // Function: reset
  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    ral.reset(kind);
    // Reset scoreboard variables
    data_out = '0;
    data_oe  = '0;
    intr_state_update_queue = {};
    data_in_update_queue = {};
    last_intr_update_except_clearing = '0;
    last_intr_test_event = '0;
    cleared_intr_bits = '0;
    first_strap_triggered = 0;
  endfunction

  // Function: check_phase
  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

endclass : ${module_instance_name}_scoreboard
