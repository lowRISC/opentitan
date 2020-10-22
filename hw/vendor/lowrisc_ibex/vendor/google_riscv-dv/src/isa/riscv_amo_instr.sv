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

class riscv_amo_instr extends riscv_instr;

  rand bit aq;
  rand bit rl;

  constraint aq_rl_c {
    (aq && rl) == 0;
  }

  `uvm_object_utils(riscv_amo_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    if (group == RV32A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".w"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else if (group == RV64A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".d"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Unexpected amo instr group: %0s / %0s",
                                 group.name(), instr_name.name()))
    end
    return get_instr_name;
  endfunction : get_instr_name

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (group inside {RV32A, RV64A}) begin
      if (instr_name inside {LR_W, LR_D}) begin
        asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
      end else begin
        asm_str = $sformatf("%0s %0s, %0s, (%0s)", asm_str, rd.name(), rs2.name(), rs1.name());
      end
    end else begin
      `uvm_fatal(`gfn, $sformatf("Unexpected amo instr group: %0s / %0s",
                                 group.name(), instr_name.name()))
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction : convert2asm

  virtual function void do_copy(uvm_object rhs);
    riscv_amo_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.aq = rhs_.aq;
    this.rl = rhs_.rl;
  endfunction : do_copy

endclass
