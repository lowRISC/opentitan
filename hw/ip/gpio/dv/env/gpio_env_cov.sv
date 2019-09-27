// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic covergroup definitions
covergroup gpio_generic_cg(string name) with function sample(bit value);
  option.per_instance = 1;
  option.name = name;
  cp_value: coverpoint value;
  cp_transitions: coverpoint value {
    bins rising  = (0 => 1);
    bins falling = (1 => 0);
  }
endgroup : gpio_generic_cg

covergroup gpio_intr_type_en_state_cg(string name) with function sample(bit intr_type,
                                                                        bit intr_en,
                                                                        bit intr_state);
  option.per_instance = 1;
  option.name = name;
  cp_cross_intr_type_en_state: cross intr_type, intr_en, intr_state {
    ignore_bins intr_type_disabled = binsof(intr_type) intersect {0};
  }
endgroup : gpio_intr_type_en_state_cg

class gpio_env_cov extends cip_base_env_cov #(.CFG_T(gpio_env_cfg));
  `uvm_component_utils(gpio_env_cov)

  // Per pin coverage for values '0' and '1' and transitions
  gpio_generic_cg gpio_pin_values_cg[NUM_GPIOS];
  // Interrupt State (Interrupt bit getting set and cleared)
  gpio_generic_cg intr_state_cg[TL_DW];
  // Interrupt Control Enable registers' values
  gpio_generic_cg intr_ctrl_en_rising_cg[TL_DW];
  gpio_generic_cg intr_ctrl_en_falling_cg[TL_DW];
  gpio_generic_cg intr_ctrl_en_lvlhigh_cg[TL_DW];
  gpio_generic_cg intr_ctrl_en_lvllow_cg[TL_DW];
  // Different gpio interrupt types' occurrences
  gpio_intr_type_en_state_cg rising_edge_intr_event_cg[TL_DW];
  gpio_intr_type_en_state_cg falling_edge_intr_event_cg[TL_DW];
  gpio_intr_type_en_state_cg lvlhigh_intr_event_cg[TL_DW];
  gpio_intr_type_en_state_cg lvllow_intr_event_cg[TL_DW];

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // Create coverage for each gpio pin value
    foreach (gpio_pin_values_cg[each_pin]) begin
      gpio_pin_values_cg [each_pin] = new($sformatf("gpio_pin-%0d", each_pin));
    end
    // Create coverage for interrupt control policies and state
    for (uint each_bit = 0; each_bit < TL_DW; each_bit++) begin
      intr_state_cg[each_bit] = new($sformatf("intr_state_cg%0d", each_bit));
      intr_ctrl_en_rising_cg[each_bit] = new($sformatf("intr_ctrl_en_rising_cg%0d", each_bit));
      intr_ctrl_en_falling_cg[each_bit] = new($sformatf("intr_ctrl_en_falling_cg%0d", each_bit));
      intr_ctrl_en_lvlhigh_cg[each_bit] = new($sformatf("intr_ctrl_en_lvlhigh_cg%0d", each_bit));
      intr_ctrl_en_lvllow_cg [each_bit] = new($sformatf("intr_ctrl_en_lvllow_cg%0d", each_bit));
      rising_edge_intr_event_cg[each_bit] = new($sformatf("rising_edge_intr_event_cg%0d",
                                                           each_bit));
      falling_edge_intr_event_cg[each_bit] = new($sformatf("falling_edge_intr_event_cg%0d",
                                                           each_bit));
      lvlhigh_intr_event_cg[each_bit] = new($sformatf("lvlhigh_intr_event_cg%0d", each_bit));
      lvllow_intr_event_cg[each_bit] = new($sformatf("lvllow_intr_event_cg%0d", each_bit));
    end
  endfunction : new

endclass
