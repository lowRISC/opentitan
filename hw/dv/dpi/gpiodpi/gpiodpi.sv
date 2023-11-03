// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gpiodpi
#(
  parameter string NAME = "gpio0",
  parameter int    N_GPIO = 32
)(
  input  logic              clk_i,
  input  logic              rst_ni,

  output logic [N_GPIO-1:0] gpio_p2d,
  input  logic [N_GPIO-1:0] gpio_d2p,
  input  logic [N_GPIO-1:0] gpio_en_d2p,
  input  logic [N_GPIO-1:0] gpio_pull_en,
  input  logic [N_GPIO-1:0] gpio_pull_sel
);
   import "DPI-C" function
     chandle gpiodpi_create(input string name, input int n_bits);

   import "DPI-C" function
     void gpiodpi_device_to_host(input chandle ctx, input logic [N_GPIO-1:0] gpio_d2p,
                                 input logic [N_GPIO-1:0] gpio_en_d2p);

   import "DPI-C" function
     void gpiodpi_close(input chandle ctx);

   import "DPI-C" function
     int gpiodpi_host_to_device_tick(input chandle ctx,
                                     input logic [N_GPIO-1:0] gpio_en_d2p,
                                     input logic [N_GPIO-1:0] gpio_pull_en,
                                     input logic [N_GPIO-1:0] gpio_pull_sel);

   chandle ctx;

   initial begin
     ctx = gpiodpi_create(NAME, N_GPIO);
   end

   final begin
     gpiodpi_close(ctx);
   end

   logic [N_GPIO-1:0] gpio_d2p_r;
   always_ff @(posedge clk_i) begin
     gpio_d2p_r <= gpio_d2p;
     if (gpio_d2p_r != gpio_d2p) begin
       gpiodpi_device_to_host(ctx, gpio_d2p, gpio_en_d2p);
     end
   end

   logic gpio_write_pulse;

   always_ff @(posedge clk_i or negedge rst_ni) begin
     if (!rst_ni) begin
       gpio_p2d <= '0; // default value
     end else begin
       gpio_p2d <= gpiodpi_host_to_device_tick(ctx, gpio_en_d2p, gpio_pull_en, gpio_pull_sel);
     end
   end

endmodule
