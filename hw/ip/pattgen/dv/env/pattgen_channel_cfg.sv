// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_channel_cfg extends uvm_object;
  `uvm_object_utils(pattgen_channel_cfg)
  `uvm_object_new

  bit                start;
  bit                stop;
  bit                enable;

  rand bit           polarity;
  rand bit [31:0]    prediv;
  rand bit [63:0]    data;
  rand bit [5:0]     len;
  rand bit [9:0]     reps;

  virtual function void reset_channel_config(string kind = "");
    start    = 1'b0;
    stop     = 1'b0;
    enable   = 1'b0;
    if (kind == "HARD") begin
      polarity = 1'b0;
      len      = 0;
      reps     = 0;
      prediv   = 0;
      data     = 0;
    end
  endfunction : reset_channel_config

  virtual function string convert2string();
      string str;

      str = {str, $sformatf("  start     %b\n",  start)};
      str = {str, $sformatf("  stop      %b\n",  stop)};
      str = {str, $sformatf("  enable    %b\n",  enable)};
      str = {str, $sformatf("  polarity  %b\n",  polarity)};
      str = {str, $sformatf("  prediv    %0d\n", prediv)};
      str = {str, $sformatf("  len       %0d\n", len)};
      str = {str, $sformatf("  reps      %0d\n", reps)};
      str = {str, $sformatf("  data[0]   %0d\n", data[31:0])};
      str = {str, $sformatf("  data[1]   %0d\n", data[63:32])};
      str = {str, $sformatf("  patt_len  %0d",   (len + 1) * (reps + 1))};
      return str;
  endfunction : convert2string

endclass : pattgen_channel_cfg
