// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface: pins_if
// Description: Pin interface for driving and sampling individual pins such as interrupts, alerts
// and gpios.
interface pins_if #(
  parameter int Width = 1
) (
  inout [Width-1:0] pins
);


  logic [Width-1:0] pins_o;       // value to be driven out
  wire  [Width-1:0] pins_int;     // value of pin using internal pull-up / pull-down
  bit   [Width-1:0] pins_oe = '0; // output enable
  bit   [Width-1:0] pins_pd = '0; // pull down enable
  bit   [Width-1:0] pins_pu = '0; // pull up enable

  // function to set pin output enable for specific pin (useful for single pin interface)
  function automatic void drive_en_pin(int idx = 0, bit val);
    pins_oe[idx] = val;
  endfunction

  // function to set pin output enable for all pins
  function automatic void drive_en(bit [Width-1:0] val);
    pins_oe = val;
  endfunction

  // function to drive a specific pin with a value (useful for single pin interface)
  function automatic void drive_pin(int idx = 0, logic val);
    pins_oe[idx] = 1'b1;
    pins_o[idx] = val;
  endfunction // drive_pin

  // function to drive all pins
  function automatic void drive(logic [Width-1:0] val);
    pins_oe = {Width{1'b1}};
    pins_o = val;
  endfunction // drive

  // function to drive all pull down values
  function automatic void set_pulldown_en(bit [Width-1:0] val);
    pins_pd = val;
  endfunction // set_pulldown_en

  // function to drive all pull up values
  function automatic void set_pullup_en(bit [Width-1:0] val);
    pins_pu = val;
  endfunction // set_pullup_en

  // function to drive the pull down value on a specific pin
  function automatic void set_pulldown_en_pin(int idx = 0, bit val);
    pins_pd[idx] = val;
  endfunction // set_pulldown_en_pin

  // function to drive the pull up value on a specific pin
  function automatic void set_pullup_en_pin(int idx = 0, bit val);
    pins_pu[idx] = val;
  endfunction // set_pullup_en_pin

  // function to sample a specific pin (useful for single pin interface)
  function automatic logic sample_pin(int idx = 0);
    return pins[idx];
  endfunction

  // function to sample all pins
  function automatic logic [Width-1:0] sample();
    return pins;
  endfunction

  // make connections
  generate
    for (genvar i = 0; i < Width; i++) begin : each_pin
      assign (pull0, pull1) pins_int[i] = pins_pd[i] ? 1'b0 :
                                          pins_pu[i] ? 1'b1 : 1'bz;
      assign pins[i] = pins_oe[i] ? pins_o[i] : pins_int[i];
    end
  endgenerate

endinterface
