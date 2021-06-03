// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_trace_item extends uvm_sequence_item;

  logic [31:0] insn_addr;
  logic [31:0] insn_data;

  // GPR operand data
  logic [31:0] gpr_operand_a;
  logic [31:0] gpr_operand_b;

  // WDR operand data
  logic [255:0] wdr_operand_a;
  logic [255:0] wdr_operand_b;

  // Flag output data
  otbn_pkg::flags_t flags_write_data [2];

  // GPR write data
  logic [31:0] gpr_write_data;

  // Enum value that shows how full the loop stack is
  loop_stack_fullness_e loop_stack_fullness;

  // The address of the last instruction of the innermost loop. Only valid if loop_stack_fullness is
  // not LoopStackEmpty.
  logic [31:0] current_loop_end;

  // Flag which is true if the current instruction is at the end of the innermost loop. This will
  // cause an if it's a jump, branch or another loop/loopi.
  logic        at_current_loop_end_insn;

  `uvm_object_utils_begin(otbn_trace_item)
    `uvm_field_int        (insn_addr,                UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (insn_data,                UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_operand_a,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_operand_b,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (wdr_operand_a,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (wdr_operand_b,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_sarray_int (flags_write_data,         UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_write_data,           UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (current_loop_end,         UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (at_current_loop_end_insn, UVM_DEFAULT)
    `uvm_field_int        (loop_stack_fullness,      UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
