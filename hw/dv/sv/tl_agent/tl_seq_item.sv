// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink sequence item
// ---------------------------------------------
class tl_seq_item extends uvm_sequence_item;

  rand bit [AddrWidth - 1   : 0] a_addr;
  rand bit [DataWidth - 1   : 0] a_data;
  rand bit [MaskWidth - 1   : 0] a_mask;
  rand bit [SizeWidth - 1   : 0] a_size;
  rand bit [2:0]                 a_param;
  rand bit [SourceWidth - 1 : 0] a_source;
  rand tl_a_op_e                 a_opcode;

  rand bit [2:0]                 d_param;
  rand bit [DataWidth - 1   : 0] d_data;
  rand bit [SourceWidth - 1 : 0] d_source;
  rand bit [SizeWidth - 1   : 0] d_size;
  rand tl_d_op_e                 d_opcode;
  rand bit                       d_error;
  rand bit [DUserWidth - 1 : 0]  d_user;
  rand bit                       d_sink;

  // host mode delays
  rand int unsigned               a_valid_delay;

  // device mode delays
  rand int unsigned               d_valid_delay;

  // param is reserved for future use, must be zero
  constraint param_c {
    a_param == 0;
    d_param == 0;
  }

  constraint no_d_error_c {
    soft d_error == 0;
  }

  constraint valid_delay_c {
    soft a_valid_delay inside {[0:50]};
    soft d_valid_delay inside {[0:50]};
  }

  // For PutFullData message, mask needs to continuous
  constraint mask_c {
    if (a_opcode == PutFullData) {
      foreach(a_mask[i]) {
        if ((i > 0) && (i < MaskWidth - 1)) {
          !a_mask[i] -> !(a_mask[i-1] && a_mask[i+1]);
        }
      }
    }
  }

  // Address alignment constraint
  // Address must be aligned to the a_size (2 ** a_size bytes)
  constraint addr_c {
    a_addr << (AddrWidth - a_size) == 0;
  }

  `uvm_object_utils_begin(tl_seq_item)
    `uvm_field_int  (a_addr,              UVM_DEFAULT)
    `uvm_field_int  (a_data,              UVM_DEFAULT)
    `uvm_field_int  (a_mask,              UVM_DEFAULT)
    `uvm_field_int  (a_size,              UVM_DEFAULT)
    `uvm_field_int  (a_param,             UVM_DEFAULT)
    `uvm_field_int  (a_source,            UVM_DEFAULT)
    `uvm_field_enum (tl_a_op_e, a_opcode, UVM_DEFAULT)
    `uvm_field_int  (d_param,             UVM_DEFAULT)
    `uvm_field_int  (d_source,            UVM_DEFAULT)
    `uvm_field_int  (d_data,              UVM_DEFAULT)
    `uvm_field_int  (d_size,              UVM_DEFAULT)
    `uvm_field_enum (tl_d_op_e, d_opcode, UVM_DEFAULT)
    `uvm_field_int  (d_error,             UVM_DEFAULT)
    `uvm_field_int  (d_sink,              UVM_DEFAULT)
    `uvm_field_int  (d_user,              UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
  endfunction : new

  virtual function string convert2string();
    string str;
    str = {$sformatf("a_addr = 0x%0h ", a_addr),
           $sformatf("a_data = 0x%0h ", a_data),
           $sformatf("a_mask = 0x%0h ", a_mask),
           $sformatf("a_size = 0x%0h ", a_size),
           $sformatf("a_param = 0x%0h ", a_param),
           $sformatf("a_source = 0x%0h ", a_source),
           $sformatf("a_opcode = %0s ", a_opcode.name()),
           $sformatf("d_data = 0x%0h ", d_data),
           $sformatf("d_size = 0x%0h ", d_size),
           $sformatf("d_param = 0x%0h ", d_param),
           $sformatf("d_source = 0x%0h ", d_source),
           $sformatf("d_opcode = %0s ", d_opcode.name()),
           $sformatf("d_error = %0b ", d_error),
           $sformatf("d_user = %0b ", d_user),
           $sformatf("d_sink = %0b ", d_sink)};
    return str;
  endfunction

  function void disable_a_chan_randomization();
    a_addr.rand_mode(0);
    a_data.rand_mode(0);
    a_mask.rand_mode(0);
    a_size.rand_mode(0);
    a_param.rand_mode(0);
    a_source.rand_mode(0);
    a_opcode.rand_mode(0);
  endfunction

  // Find whether this seq item is a read or a write.
  virtual function bit is_write();
    return (a_opcode inside {PutFullData, PutPartialData});
  endfunction

  // Check if d_opcode is appropriate for the given a_opcode. This check assumes that the
  // response packet has been appended with the corresponding request.
  virtual function bit check_opcodes(bit throw_error = 1'b1);
    tl_d_op_e exp_d_opcode = is_write() ? tlul_pkg::AccessAck : tlul_pkg::AccessAckData;
    check_opcodes = (d_opcode == exp_d_opcode);
    if (!check_opcodes && throw_error) begin
      `uvm_error(`gfn, $sformatf("d_opcode: %0s & exp_d_opcode: %0s mismatch",
                                  d_opcode, exp_d_opcode))
    end
  endfunction

  // Check if packet parameters are ok.
  virtual function bit is_ok(bit throw_error = 1'b1);
    is_ok = 1'b1;
    is_ok &= check_opcodes(throw_error);
    // addr and data channels should have the same source
    is_ok &= (a_source == d_source);
    if (!is_ok && throw_error)
      `uvm_error(`gfn, $sformatf("a_source: 0x%0h & d_source: 0x%0h mismatch", a_source, d_source))
  endfunction

endclass
