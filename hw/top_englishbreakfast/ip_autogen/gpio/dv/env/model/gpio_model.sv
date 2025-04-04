// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_model #(int NUM_GPIOS = 32) extends uvm_component;

  `uvm_component_param_utils(gpio_model#(NUM_GPIOS))

  logic  [NUM_GPIOS - 1:0] i_gpio_in;
  logic  [NUM_GPIOS - 1:0] oe_gpio_out;
  logic  [NUM_GPIOS - 1:0] o_gpio_out;
  bit active;

  typedef logic [NUM_GPIOS - 1:0] pins_t;

  // Local variables
  logic [NUM_GPIOS - 1:0] gpio_i_driven;

  // gpio config env object;
  local gpio_env_cfg cfg;

  // Constructor
  function new(string name = "gpio_model", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Function: Build phase function
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null, "uvm_test_top.env", "cfg", cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end

  endfunction

  // Function: Evaluate gpio input driven to dut.
  function automatic pins_t evaluate_data_in_out(gpio_seq_item item);
    foreach (item.cio_gpio_oe[pin_num]) begin
      if (item.cio_gpio_oe[pin_num] == 1'b1) begin
        gpio_i_driven[pin_num] = item.cio_gpio_o[pin_num];
      end else begin
        gpio_i_driven[pin_num] = 1'bz;
      end

      `uvm_info(`gfn, $sformatf("pins_oe[%0d] = %0b pins_o[%0d] = %0b gpio_i_driven[%0d] = %0b",
      pin_num, item.cio_gpio_oe[pin_num], pin_num,
      item.cio_gpio_o[pin_num], pin_num, gpio_i_driven[pin_num]),
      UVM_HIGH)

      return gpio_i_driven;
    end
  endfunction

  // Function: process the gpio input pins interface
  // gpio_i_transition
  // Flag to indicate:
  // (i) if there was any change in value on gpio_i pin - Bit0
  // (ii) what change occurred on gpio_i pin - Bit1
  function automatic void process_gpio_transition (ref
    gpio_transition_t [NUM_GPIOS-1:0] gpio_i_transition);

    logic [NUM_GPIOS-1:0] prev_gpio_i;
    prev_gpio_i = cfg.gpio_vif.pins;

    foreach (prev_gpio_i[pin]) begin
      gpio_i_transition[pin].transition_occurred =
      (cfg.gpio_vif.pins[pin] !== prev_gpio_i[pin]);
      if (gpio_i_transition[pin].transition_occurred) begin
        case (cfg.gpio_vif.pins[pin])
          1'b0: begin
            // Negedge seen on pin, indicated by 0 value
            gpio_i_transition[pin].is_rising_edge = 1'b0;
          end
          1'b1: begin
            // Posedge seen on pin, indicated by 1 value
            gpio_i_transition[pin].is_rising_edge = 1'b1;
          end
          1'bz: begin
            if (prev_gpio_i[pin] === 1'b1) begin
              // Negedge seen on pin, indicated by 0 value
              gpio_i_transition[pin].is_rising_edge = 1'b0;
            end else if (prev_gpio_i[pin] === 1'b0) begin
              // Posedge seen on pin, indicated by 1 value
              gpio_i_transition[pin].is_rising_edge = 1'b1;
            end else begin
              // x->z does not indicate useful transition, reset transition bit
              gpio_i_transition[pin].transition_occurred = 1'b0;
            end
          end
          1'bx: begin
            if (prev_gpio_i[pin] === 1'b1) begin
              // Negedge seen on pin, indicated by 0 value
              gpio_i_transition[pin].is_rising_edge = 1'b0;
            end else if (prev_gpio_i[pin] === 1'b0) begin
              // Posedge seen on pin, indicated by 1 value
              gpio_i_transition[pin].is_rising_edge = 1'b1;
            end else begin
              // z->x does not indicate useful transition, reset transition bit
              gpio_i_transition[pin].transition_occurred = 1'b0;
            end
          end
          default: begin
            `uvm_info(`gfn, "gpio pin undefined!", UVM_HIGH)
          end
        endcase
      end
    end
    foreach (gpio_i_transition[ii]) begin
      `uvm_info(`gfn, $sformatf("gpio_i_transition[%0d] = %0p", ii, gpio_i_transition[ii]),
      UVM_HIGH)
    end
endfunction
endclass : gpio_model


