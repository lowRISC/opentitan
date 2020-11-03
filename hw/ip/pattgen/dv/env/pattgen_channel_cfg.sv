// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_channel_cfg extends uvm_object;
  `uvm_object_utils(pattgen_channel_cfg)
  `uvm_object_new

  bit                start;
  bit                done;
  bit                enable;
  rand bit           polarity;
  rand bit [31:0]    prediv;
  rand bit [63:0]    data;
  rand bit [5:0]     len;
  rand bit [9:0]     reps;

  // functions
  virtual function void reset_channel_config();
    start    = 1'b0;
    done     = 1'b0;
  endfunction : reset_channel_config

  // this function print channel configuration for debug
  virtual function void print_config(string msg, bit do_print = 1'b0);
    string str;

    if (do_print) begin
      str = {msg, "\n"};
      str = {str, $sformatf("    polarity    %b\n",  polarity)};
      str = {str, $sformatf("    prediv      %0d\n", prediv)};
      str = {str, $sformatf("    len         %0d\n", len)};
      str = {str, $sformatf("    reps        %0d\n", reps)};
      str = {str, $sformatf("    data[0]     %0d\n", data[31:0])};
      str = {str, $sformatf("    data[1]     %0d\n", data[63:32])};
      str = {str, $sformatf("    patt_len    %0d",   len * reps)};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
    end
  endfunction : print_config

endclass : pattgen_channel_cfg