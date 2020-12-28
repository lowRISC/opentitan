// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import gpio_env_pkg::*;
  import gpio_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [NUM_GPIOS-1:0] gpio_pins;
  wire [NUM_GPIOS-1:0] gpio_i;
  wire [NUM_GPIOS-1:0] gpio_o;
  wire [NUM_GPIOS-1:0] gpio_oe;
  wire [NUM_GPIOS-1:0] gpio_intr;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if(.pins(interrupts));
  pins_if #(1) devmode_if(.pins(devmode));
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_GPIOS) gpio_if(.pins(gpio_pins));

  // dut
  gpio dut (
    .clk_i                (clk        ),
    .rst_ni               (rst_n      ),

    .tl_i                 (tl_if.h2d  ),
    .tl_o                 (tl_if.d2h  ),

    .cio_gpio_i           (gpio_i     ),
    .cio_gpio_o           (gpio_o     ),
    .cio_gpio_en_o        (gpio_oe    ),

    .intr_gpio_o          (gpio_intr  )
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
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pins_if #(NUM_GPIOS))::set(null, "*.env", "gpio_vif", gpio_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
