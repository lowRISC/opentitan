// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import ${module_instance_name}_env_pkg::*;
  import ${module_instance_name}_test_pkg::*;
  import ${module_instance_name}_reg_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire [NUM_GPIOS-1:0] gpio_pins;
  wire [NUM_GPIOS-1:0] gpio_i;
  wire [NUM_GPIOS-1:0] gpio_o;
  wire [NUM_GPIOS-1:0] gpio_oe;
  wire [NUM_GPIOS-1:0] gpio_intr;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  gpio_straps_t sampled_straps;
  wire strap_en;

  `DV_ALERT_IF_CONNECT()

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  pins_if #(NUM_MAX_INTERRUPTS) intr_if (.pins(interrupts));
  ${module_instance_name}_straps_if straps_if_inst (
    .clk  (clk),
    .rst_n(rst_n)
  );
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  pins_if #(NUM_GPIOS) gpio_if (.pins(gpio_pins));

  // dut
  ${module_instance_name} #(
    // We have two build modes in this testbench: one with CDC synchronizers enabled, and one
    // where they are disabled.
`ifdef GPIO_ASYNC_ON
    .GpioAsyncOn(1)
`else
    .GpioAsyncOn(0)
`endif
  ) dut (
    .clk_i (clk),
    .rst_ni(rst_n),

    .strap_en_i(straps_if_inst.strap_en),
    .sampled_straps_o(straps_if_inst.sampled_straps),

    .tl_i(tl_if.h2d),
    .tl_o(tl_if.d2h),

    .intr_gpio_o(gpio_intr),

    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    // RACL interface
    .racl_policies_i('0),
    .racl_error_o   (  ),

    .cio_gpio_i          (gpio_i),
    .cio_gpio_o          (gpio_o),
    .cio_gpio_en_o       (gpio_oe)
  );

  assign interrupts[NUM_GPIOS-1:0] = gpio_intr;

  // gpio pins are represented by bi-directional gpio_if interface
  // drive the pins only if en_o bit from the dut is high
  assign gpio_i = gpio_pins[NUM_GPIOS-1:0];
  for (genvar i = 0; i < NUM_GPIOS; i++) begin : gen_each_gpio
    assign gpio_pins[i] = gpio_oe[i] ? gpio_o[i] : 1'bz;
  end : gen_each_gpio

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pins_if #(NUM_GPIOS))::set(null, "*.env", "gpio_vif", gpio_if);
    uvm_config_db#(virtual ${module_instance_name}_straps_if)::set(null, "*.*", "straps_vif", straps_if_inst);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
