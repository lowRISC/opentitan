// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// We are enclosing generic covergroups inside class so that we can
// take avoid tool limitation of not allowing arrays of covergroup
// Refer to Issue#375 for more details
class gpio_intr_type_cov_obj extends uvm_object;
  `uvm_object_utils(gpio_intr_type_cov_obj)

  // Covergroup: intr_type_cg
  // Covergroup for different interrupt types based on "Interrupt Control" registers in
  // gpio. This group samples combination of interrupt type, interrupt enable and
  // interrupt state, on per bit basis.
  covergroup intr_type_cg(string name) with function sample(bit type_ctrl_en,
                                                            bit intr_en,
                                                            bit intr_state);
    option.per_instance = 1;
    option.name = name;
    cp_cross_type_en_state: cross type_ctrl_en, intr_en, intr_state {
      ignore_bins intr_type_disabled = binsof(type_ctrl_en) intersect {0};
    }
  endgroup : intr_type_cg

  // Function: new
  function new(string name="gpio_intr_type_cov_obj");
    super.new(name);
    intr_type_cg = new(name);
  endfunction : new
endclass : gpio_intr_type_cov_obj

class gpio_out_oe_cov_obj extends uvm_object;
  `uvm_object_utils(gpio_out_oe_cov_obj)

  // Covergroup: var1_var2_cg
  // Covergroup invovling two variables of bit type and are meant to
  // be used for cross coverage related to *out* and *oe* registers
  covergroup var1_var2_cg(string name) with function sample(bit var1, bit var2);
    option.per_instance = 1;
    option.name = name;
    cp_var1: coverpoint var1;
    cp_var2: coverpoint var2;
    cp_var1_var2_cross: cross cp_var1, cp_var2;
  endgroup : var1_var2_cg

  // Function: new
  function new(string name="gpio_out_oe_cov_obj");
    super.new(name);
    var1_var2_cg = new(name);
  endfunction : new
endclass : gpio_out_oe_cov_obj

class gpio_env_cov extends cip_base_env_cov #(.CFG_T(gpio_env_cfg));
  `uvm_component_utils(gpio_env_cov)

  // Array of coverage objects for per pin coverage for gpio pin values
  bit_toggle_cg_wrap gpio_pin_values_cov_obj[NUM_GPIOS];
  // Interrupt State (Interrupt bit getting set and cleared)
  bit_toggle_cg_wrap intr_state_cov_obj[NUM_GPIOS];
  // Interrupt Control Enable registers' values
  bit_toggle_cg_wrap intr_ctrl_en_cov_objs[NUM_GPIOS][string];
  // data_in register per bit value coverage
  bit_toggle_cg_wrap data_in_cov_obj[NUM_GPIOS];
  // Per bit coverage on *out* and *oe* registers
  bit_toggle_cg_wrap out_oe_cov_objs[NUM_GPIOS][string];
  // Different gpio interrupt types' occurrences
  gpio_intr_type_cov_obj intr_event_type_cov_objs[NUM_GPIOS][string];
  // Coverage on data and mask fields of masked* registers
  gpio_out_oe_cov_obj out_oe_mask_data_cov_objs[NUM_GPIOS/2][string];
  // Coverage on effective values of DATA_OUT and DATA_OE
  gpio_out_oe_cov_obj data_out_data_oe_cov_obj[NUM_GPIOS];
  // Cross Coverage between per pin values of data_out value, data_oe value
  // and data_in value
  covergroup data_out_data_oe_data_in_cross_cg(string name) with function sample(uint pin,
                                                                                 bit data_out,
                                                                                 bit data_oe,
                                                                                 bit data_in);
    option.name = name;
    cp_pin: coverpoint pin {
      bins bins_for_gpio_bits[] = {[0:NUM_GPIOS-1]};
    }
    cp_cross_all: cross cp_pin, data_out, data_oe, data_in {
      // If data_oe is true, data_in cannot be different from data_out value
      illegal_bins data_oe_1_data_out_0_data_in_1 = binsof(data_out) intersect {0} &&
                                                    binsof(data_oe)  intersect {1} &&
                                                    binsof(data_in)  intersect {1};
      illegal_bins data_oe_1_data_out_1_data_in_0 = binsof(data_out) intersect {1} &&
                                                    binsof(data_oe)  intersect {1} &&
                                                    binsof(data_in)  intersect {0};
    }
  endgroup : data_out_data_oe_data_in_cross_cg
  // Cross coverage between gpio pin value and effective data_in value
  covergroup gpio_pins_data_in_cross_cg(string name) with function sample(uint pin,
                                                                          bit gpio_value,
                                                                          bit data_in);
    option.name = name;
    cp_pin: coverpoint pin {
      bins bins_for_gpio_bits[] = {[0:NUM_GPIOS-1]};
    }
    cp_cross_pins_data_in: cross cp_pin, gpio_value, data_in;
  endgroup : gpio_pins_data_in_cross_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    begin
      string intr_types[4] = '{"rising", "falling", "lvlhigh", "lvllow"};
      string out_oe_reg_names[6] = '{"direct_out",
                                     "direct_oe",
                                     "masked_out_lower",
                                     "masked_oe_lower",
                                     "masked_out_upper",
                                     "masked_oe_upper"};
      foreach (intr_state_cov_obj[each_pin]) begin
        // Create coverage for each gpio pin values and transitions
        gpio_pin_values_cov_obj[each_pin] = new($sformatf("gpio_values_cov_obj_pin%0d", each_pin));
        // Create per pin coverage for interrupt state values and transitions
        intr_state_cov_obj[each_pin] = new($sformatf("intr_state_cov_obj_pin%0d", each_pin));
        // Create per pin coverage interrupts
        foreach(intr_types[each_type]) begin
          // Per pin coverage for "Intrrupt Control Enable" values
          // and transitions for each type of interrupt
          intr_ctrl_en_cov_objs[each_pin][{"intr_ctrl_en_", intr_types[each_type]}] =
              new({"intr_ctrl_en_", intr_types[each_type], $sformatf("_pin%0d_cov", each_pin)});
          // Per pin coverage for different types of interrupt event occurrences
          intr_event_type_cov_objs[each_pin][{"intr_event_", intr_types[each_type]}] =
              new({"intr_event_", intr_types[each_type], $sformatf("_pin%0d", each_pin)});
        end
        // Per pin coverage for values of different *out* and *oe* registers
        foreach (out_oe_reg_names[each_reg]) begin
          out_oe_cov_objs[each_pin][out_oe_reg_names[each_reg]] =
            new({out_oe_reg_names[each_reg], $sformatf("_cov_obj_pin%0d", each_pin)});
        end
        data_out_data_oe_cov_obj[each_pin] = new($sformatf("data_out_data_oe_cov_obj_pin%0d",
                                                           each_pin));
        data_in_cov_obj[each_pin] = new($sformatf("data_in_cov_obj_pin%0d", each_pin));
        // Create sticky interrupt coverage per pin
        // No toggle coverage is required in this case, so specify toggle_cov_en = 0
        sticky_intr_cov[{"gpio_sticky_intr_pin", $sformatf("%0d", each_pin)}] =
            new(.name({"gpio_sticky_intr_pin", $sformatf("%0d", each_pin)}), .toggle_cov_en(0));
      end
      // Per pin coverage and cross coverage for mask and data
      // fields within masked_* registers
      foreach (out_oe_mask_data_cov_objs[each_pin]) begin
        foreach (out_oe_reg_names[each_reg]) begin
          if (!uvm_re_match("masked*", out_oe_reg_names[each_reg])) begin
            out_oe_mask_data_cov_objs[each_pin][out_oe_reg_names[each_reg]] =
                new({out_oe_reg_names[each_reg], $sformatf("_mask_data_cov_obj_pin%0d", each_pin)});
          end
        end
      end
      data_out_data_oe_data_in_cross_cg = new("data_out_data_oe_data_in_cross_cg");
      gpio_pins_data_in_cross_cg = new("gpio_pins_data_in_cross_cg");
    end
  endfunction : new

endclass
