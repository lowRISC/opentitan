/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Silicon Labs, Inc.
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
class riscv_zba_instr extends riscv_instr;
  `uvm_object_utils(riscv_zba_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
  endfunction

  virtual function void set_imm_len();
    if (!(instr_name inside {SLLI_UW})) begin
      imm_len = $clog2(XLEN) - 1;
    end else begin
      imm_len = $clog2(XLEN);
    end
    imm_mask = imm_mask << imm_len;
  endfunction : set_imm_len

  function bit[6:0] get_opcode();
    case (instr_name) inside
      SH1ADD, SH2ADD, SH3ADD :          get_opcode = 7'b0110011;
      SH1ADD_UW, SH2ADD_UW, SH3ADD_UW : get_opcode = 7'b0111011;
      SLLI_UW :                         get_opcode = 7'b0011011;
      default :                         get_opcode = super.get_opcode();
    endcase
  endfunction : get_opcode

  virtual function bit [2:0] get_func3();
    case (instr_name) inside
      ADD_UW    : get_func3 = 3'b000;
      SH1ADD    : get_func3 = 3'b010;
      SH2ADD    : get_func3 = 3'b100;
      SH3ADD    : get_func3 = 3'b110;
      SH1ADD_UW : get_func3 = 3'b010;
      SH2ADD_UW : get_func3 = 3'b100;
      SH3ADD_UW : get_func3 = 3'b110;
      SLLI_UW   : get_func3 = 3'b001;
      default   : get_func3 = super.get_func3();
    endcase
  endfunction : get_func3

  function bit [6:0] get_func7();
    case (instr_name) inside
      ADD_UW    : get_func7 = 7'b0000100;
      SH1ADD    : get_func7 = 7'b0010000;
      SH2ADD    : get_func7 = 7'b0010000;
      SH3ADD    : get_func7 = 7'b0010000;
      SH1ADD_UW : get_func7 = 7'b0010000;
      SH2ADD_UW : get_func7 = 7'b0010000;
      SH3ADD_UW : get_func7 = 7'b0010000;
      SLLI_UW   : get_func7 = 7'b0010000;
      default   : get_func7 = super.get_func7();
    endcase
  endfunction : get_func7

  virtual function string convert2bin(string prefix = "");
    string binary = "";
    if (instr_name inside {SLLI_UW}) begin
      binary = $sformatf("%8h", {5'b0_0001, imm[6:0], rs1, get_func3(), rd, get_opcode()});
    end
    else begin
      binary = super.convert2bin(prefix);
    end
  endfunction : convert2bin

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zba_extension &&
           (RV32ZBA inside { supported_isa } || RV64ZBA inside { supported_isa }) &&
           instr_name inside {
             ADD_UW,
             SH1ADD, SH1ADD_UW,
             SH2ADD, SH2ADD_UW,
             SH3ADD, SH3ADD_UW,
             SLLI_UW
           });
  endfunction : is_supported

endclass : riscv_zba_instr



