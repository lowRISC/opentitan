// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// One complete OTP macro transaction: the request otp_ctrl sends and the response it gets back.
//
// A sequence randomizes the request fields. The driver sends the request and, once the response
// arrives, copies it into rdata and err, so the sequence can read it after finish_item(). The
// monitor builds its own copy of the whole transaction for the scoreboard.
class otp_macro_item extends uvm_sequence_item;

  // Request
  rand cmd_e            cmd;
  rand otp_macro_size_t size;   // Number of OTP words minus one.
  rand otp_macro_addr_t addr;   // OTP word address.
  rand otp_macro_data_t wdata;

  // Response
  otp_macro_data_t rdata;
  err_e            err;

  // Commands otp_ctrl sends after Init. Init itself is sent on purpose, not picked at random.
  constraint cmd_c {
    soft cmd inside {Read, Write, ReadRaw, WriteRaw, Zeroize};
  }

  // otp_ctrl only ever moves 1, 2 or 4 words at a time, aligned to the transfer size.
  constraint size_c {
    soft size inside {0, 1, 3};
  }
  constraint addr_c {
    (addr % (size + 1)) == 0;
    (addr + size) < OtpDepth;
  }

  `uvm_object_utils_begin(otp_macro_item)
    `uvm_field_enum(cmd_e, cmd, UVM_DEFAULT)
    `uvm_field_int (size,       UVM_DEFAULT | UVM_DEC)
    `uvm_field_int (addr,       UVM_DEFAULT)
    `uvm_field_int (wdata,      UVM_DEFAULT)
    `uvm_field_int (rdata,      UVM_DEFAULT)
    `uvm_field_enum(err_e, err, UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new(string name = "");

  // Returns word `idx` (0 to size) of wdata or rdata.
  extern function bit [OtpWidth-1:0] get_wdata_word(int unsigned idx);
  extern function bit [OtpWidth-1:0] get_rdata_word(int unsigned idx);
endclass : otp_macro_item

function otp_macro_item::new(string name = "");
  super.new(name);
endfunction : new

function bit [OtpWidth-1:0] otp_macro_item::get_wdata_word(int unsigned idx);
  return wdata[idx * OtpWidth +: OtpWidth];
endfunction : get_wdata_word

function bit [OtpWidth-1:0] otp_macro_item::get_rdata_word(int unsigned idx);
  return rdata[idx * OtpWidth +: OtpWidth];
endfunction : get_rdata_word
