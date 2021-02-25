// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_item extends uvm_sequence_item;

  // TODO: create
  `uvm_object_utils_begin(csrng_item)
  `uvm_object_utils_end

  `uvm_object_new

  acmd_e       acmd;
  bit [3:0]    clen, flags;
  bit [18:0]   glen;

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |********** csrng_item **********| \t")             };
    str = {str,  $sformatf("\n\t |* acmd   :   %4s              *| \t", acmd.name()) };
    str = {str,  $sformatf("\n\t |********************************| \t")             };
    str = {str, "\n"};
    return str;
  endfunction

endclass
