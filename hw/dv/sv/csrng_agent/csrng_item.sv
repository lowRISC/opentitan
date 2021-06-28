// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_item extends uvm_sequence_item;

  `uvm_object_utils_begin(csrng_item)
  `uvm_object_utils_end

  `uvm_object_new

  rand acmd_e       acmd;
  rand bit [3:0]    clen, flags;
  rand bit [18:0]   glen;
  rand bit [31:0]   cmd_data_q[$];

  // TODO: Try clen > 12
  constraint c_clen {
    clen inside {[0:12]};
  };

  constraint c_cmd_data {
    solve clen before cmd_data_q;

    cmd_data_q.size() == clen;
  };

  constraint c_flags {
    flags inside {[0:1]};
  };

// TODO: add/fix glen constraint
//  constraint c_glen {
//    solve acmd before glen;
//
//    if (acmd != csrng_pkg::GEN)
//      glen == 'h0;
//  };

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |*********** csrng_item ************| \t")                   };
    str = {str,  $sformatf("\n\t |* acmd           :  %4s          *| \t", acmd.name())       };
    str = {str,  $sformatf("\n\t |* clen           :   0x%0h          *| \t", clen)           };
    str = {str,  $sformatf("\n\t |* flags          :   0x%0h          *| \t", flags)          };
    str = {str,  $sformatf("\n\t |* glen           :   0x%5h      *| \t", glen)               };
    if (cmd_data_q.size()) begin
      for (int i = 0; i < cmd_data_q.size(); i++) begin
        str = {str,  $sformatf("\n\t |* cmd_data_q[%2d] :   0x%0h   *| \t", i, cmd_data_q[i]) };
      end
    end
    str = {str,  $sformatf("\n\t |***********************************| \t")                   };
    str = {str, "\n"};
    return str;
  endfunction

endclass
