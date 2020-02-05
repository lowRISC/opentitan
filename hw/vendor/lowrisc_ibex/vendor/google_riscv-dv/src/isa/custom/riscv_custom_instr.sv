/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Custom instruction class

class riscv_custom_instr extends riscv_instr;

  // TODO: Add custom operands here, example:
  // rand riscv_reg_t rs3;

  `uvm_object_utils(riscv_custom_instr)
  `uvm_object_new

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    // TODO: Add custom instruction name encoding here
    return get_instr_name;
  endfunction : get_instr_name

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string("nop", MAX_INSTR_STR_LEN);
    /* TODO: Convert custom instruction to assembly format. Example:
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case (instr_name)
      CUSTOM_1: asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
      CUSTOM_2: asm_str = $sformatf("%0s %0s", asm_str, r3.name());
    endcase
    */
    comment = {get_instr_name(), " ", comment};
    if (comment != "") begin
      asm_str = {asm_str, " #",comment};
    end
    return asm_str.tolower();
  endfunction : convert2asm

endclass : riscv_custom_instr
