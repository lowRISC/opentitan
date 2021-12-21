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
class riscv_zbc_instr extends riscv_instr;
  `uvm_object_utils(riscv_zbc_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
  endfunction : pre_randomize

  function bit[6:0] get_opcode();
    case (instr_name) inside
      CLMUL,
      CLMULH,
      CLMULR  : get_opcode = 7'b011_0011;
      default : get_opcode = super.get_opcode();
    endcase
  endfunction : get_opcode

  function bit [2:0] get_func3();
    case (instr_name) inside
      CLMUL   : get_func3 = 3'b001;
      CLMULH  : get_func3 = 3'b011;
      CLMULR  : get_func3 = 3'b010;
      default : get_func3 = super.get_func3();
    endcase
  endfunction : get_func3

  function bit [6:0] get_func7();
    case (instr_name) inside
      CLMUL   : get_func7 = 7'b000_0101;
      CLMULH  : get_func7 = 7'b000_0101;
      CLMULR  : get_func7 = 7'b000_0101;
      default : get_func7 = super.get_func7();
    endcase
  endfunction : get_func7

  virtual function string convert2bin(string prefix = "");
    string binary = "";
    if (instr_name inside {CLMUL, CLMULH, CLMULR}) begin
      binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
    end
    else begin
      binary = super.convert2bin(prefix);
    end
  endfunction : convert2bin

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zbc_extension &&
           (RV32ZBC inside { supported_isa } || RV64ZBC inside { supported_isa }) &&
            instr_name inside {
              CLMUL, CLMULH, CLMULR
            });
  endfunction : is_supported

endclass : riscv_zbc_instr
