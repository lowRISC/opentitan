// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_item extends uvm_sequence_item;

  `uvm_object_utils_begin(csrng_item)
  `uvm_object_utils_end

  `uvm_object_new

  rand acmd_e       acmd;
  rand mubi4_t      flags;
  rand bit [3:0]    clen;
  rand bit [11:0]   glen;
  rand bit [31:0]   cmd_data_q[$];

  bit               fips;
  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]   genbits_q[$];

  constraint c_clen {
    clen inside {[0:12]};
  }

  constraint c_cmd_data {
    solve clen before cmd_data_q;
    cmd_data_q.size() == clen;
  }

  constraint c_flags {
    flags inside {MuBi4True, MuBi4False};
  }

  constraint c_glen {
    glen dist {
      // TODO(#18350): Add a bin for 0 (with 5% chance, like for 4095?).
      [1:32]      :/ 75,
      [33:128]    :/ 10,
      [129:1024]  :/ 5,
      [1025:4094] :/ 5,
      4095        := 5
    };
  }

   //--------------------------------------------------------------------
   // do_copy
   //--------------------------------------------------------------------
   virtual function void do_copy(uvm_object rhs);
      csrng_item   rhs_;
      $cast(rhs_, rhs);
      super.do_copy(rhs);

      this.acmd       = rhs_.acmd;
      this.clen       = rhs_.clen;
      this.flags      = rhs_.flags;
      this.glen       = rhs_.glen;
      this.fips       = rhs_.fips;
      this.cmd_data_q = rhs_.cmd_data_q;
      this.genbits_q  = rhs_.genbits_q;
   endfunction

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |********* csrng_item **********| \t")                   };
    str = {str,  $sformatf("\n\t |* acmd           :      %5s *| \t", acmd.name())        };
    str = {str,  $sformatf("\n\t |* clen           :      %5d *| \t", clen)               };
    str = {str,  $sformatf("\n\t |* flags[0]       :      %5d *| \t", flags[0])           };
    str = {str,  $sformatf("\n\t |* glen           :      %5d *| \t", glen)               };
    str = {str,  $sformatf("\n\t |* fips           :      %5d *| \t", fips)               };
    for (int i = 0; i < cmd_data_q.size(); i++) begin
      str = {str,  $sformatf("\n\t |* cmd_data_q[%2d] : 0x%8h *| \t", i, cmd_data_q[i]) };
    end
    for (int i = 0; i < genbits_q.size(); i++) begin
      str = {str,  $sformatf("\n\t |* genbits_q[%2d]  : 0x%8h *| \t", i, genbits_q[i]) };
    end
    str = {str,  $sformatf("\n\t |*******************************| \t")                   };
    str = {str, "\n"};
    return str;
  endfunction

endclass
