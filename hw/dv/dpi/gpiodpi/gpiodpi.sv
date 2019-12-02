// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gpiodpi
#(
  parameter string NAME = "gpio0",
  parameter        N_GPIO = 32
)(
  input  logic              clk_i,
  input  logic              rst_ni,

  output logic [N_GPIO-1:0] gpio_p2d,
  input  logic [N_GPIO-1:0] gpio_d2p,
  input  logic [N_GPIO-1:0] gpio_en_d2p
);
   import "DPI-C" function
     chandle gpiodpi_create(input string name, input int n_bits);

   import "DPI-C" function
     void gpiodpi_device_to_host(input chandle ctx, input [N_GPIO-1:0] gpio_d2p,
                                 input [N_GPIO-1:0] gpio_en_d2p);

   import "DPI-C" function
     void gpiodpi_close(input chandle ctx);

   import "DPI-C" function
     int gpiodpi_host_to_device_tick(input chandle ctx,
                                     input [N_GPIO-1:0] gpio_en_d2p);

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
     end else if (gpio_write_pulse) begin
       gpio_p2d <= gpiodpi_host_to_device_tick(ctx, gpio_en_d2p);
     end
   end

   // gpiodpio_host_to_device_tick() will be called every MAX_COUNT
   // clock posedges; this should be kept reasonably high, since each
   // tick call will perform at least one syscall.
   localparam MAX_COUNT = 2048;
   logic [$clog2(MAX_COUNT)-1:0] counter;

   assign gpio_write_pulse = counter == MAX_COUNT -1;

   always_ff @(posedge clk_i or negedge rst_ni) begin
     if (!rst_ni) begin
       counter <= '0;
     end else if (gpio_write_pulse) begin
       counter <= '0;
     end else begin
       counter <= counter + 1'b1;
     end
   end

endmodule
