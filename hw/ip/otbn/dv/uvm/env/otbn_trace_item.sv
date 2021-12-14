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

  // Flag read/write data
  otbn_pkg::flags_t flags_read_data [2];
  logic [1:0]       flags_write_valid;
  otbn_pkg::flags_t flags_write_data [2];

  // GPR and WDR write data
  logic [31:0]  gpr_write_data;
  logic [255:0] wdr_write_data;

  // Flags showing call stack pushes and pops
  call_stack_flags_t call_stack_flags;

  // Enum values that show how full the loop and call stacks are
  stack_fullness_e loop_stack_fullness;
  stack_fullness_e call_stack_fullness;

  // Is the sideload key valid?
  logic has_sideload_key;

  // The address of the last instruction of the innermost loop. Only valid if loop_stack_fullness is
  // not StackEmpty.
  logic [31:0] current_loop_end;

  // Flag which is true if the current instruction is at the end of the innermost loop. This will
  // cause an if it's a jump, branch or another loop/loopi.
  logic        at_current_loop_end_insn;

  // MOD ispr
  logic [255:0] mod;

  // Intermediate value for MULQACC instructions
  logic [256:0] new_acc_extended;

  `uvm_object_utils_begin(otbn_trace_item)
    `uvm_field_int        (insn_addr,                UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (insn_data,                UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_operand_a,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_operand_b,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (wdr_operand_a,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (wdr_operand_b,            UVM_DEFAULT | UVM_HEX)
    `uvm_field_sarray_int (flags_read_data,          UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (flags_write_valid,        UVM_DEFAULT | UVM_BIN)
    `uvm_field_sarray_int (flags_write_data,         UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (gpr_write_data,           UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (wdr_write_data,           UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (call_stack_flags,         UVM_DEFAULT)
    `uvm_field_enum       (stack_fullness_e, loop_stack_fullness, UVM_DEFAULT)
    `uvm_field_enum       (stack_fullness_e, call_stack_fullness, UVM_DEFAULT)
    `uvm_field_int        (current_loop_end,         UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (at_current_loop_end_insn, UVM_DEFAULT)
    `uvm_field_int        (mod,                      UVM_DEFAULT | UVM_HEX)
    `uvm_field_int        (new_acc_extended,         UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new
endclass
