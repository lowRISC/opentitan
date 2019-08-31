// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gpiodpi
#(
  parameter string NAME = "gpio0",
  parameter        N_GPIO = 32
)(
  input               clk_i,
  input               rst_ni,

  output [N_GPIO-1:0] gpio_p2d,
  input [N_GPIO-1:0]  gpio_d2p,
  input [N_GPIO-1:0]  gpio_en_d2p
);
   import "DPI-C" function
     chandle gpiodpi_create(input string name, input int n_bits);

   import "DPI-C" function
     void gpiodpi_device_to_host(input chandle ctx, input [N_GPIO-1:0] gpio_d2p,
                                 input [N_GPIO-1:0] gpio_en_d2p);

   import "DPI-C" function
     void gpiodpi_close(input chandle ctx);

   export "DPI-C" function
     gpiodpi_host_to_device;

   function void gpiodpi_host_to_device(input [N_GPIO-1:0] gpio_p2d_set);
     gpio_p2d = gpio_p2d_set;
   endfunction

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

endmodule
