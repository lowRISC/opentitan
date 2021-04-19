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
  bit [31:0]   cmd_data[$];

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |********** csrng_item **********| \t")             };
    str = {str,  $sformatf("\n\t |* acmd   :   %4s              *| \t", acmd.name()) };
    str = {str,  $sformatf("\n\t |* clen   :   %4h              *| \t", clen)        };
    str = {str,  $sformatf("\n\t |* flags  :   %4h              *| \t", flags)       };
    str = {str,  $sformatf("\n\t |* glen   :   %19h             *| \t", glen)        };
    if (cmd_data.size()) begin
      do begin
        str = {str,  $sformatf("\n\t |* cmd_data[%0d]   :   %0h             *| \t", cmd_data.size(), cmd_data.pop_front())        };
      end
      while (cmd_data.size());
    end
    str = {str,  $sformatf("\n\t |********************************| \t")             };
    str = {str, "\n"};
    return str;
  endfunction

endclass
