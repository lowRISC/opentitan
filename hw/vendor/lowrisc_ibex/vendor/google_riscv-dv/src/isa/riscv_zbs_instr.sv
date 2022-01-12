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
class riscv_zbs_instr extends riscv_instr;
  `uvm_object_utils(riscv_zbs_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
  endfunction : pre_randomize

  function bit is_rv64();
    is_rv64 = (group == RV64B);
  endfunction : is_rv64

  virtual function void set_imm_len();
    if (format inside {I_FORMAT}) begin
      if (instr_name inside { BCLRI, BEXTI, BINVI, BSETI }) begin
        imm_len = $clog2(XLEN);
      end
    end
    imm_mask = imm_mask << imm_len;
  endfunction : set_imm_len

  function bit [6:0] get_opcode();
    case (instr_name) inside
      BCLR,  BEXT,  BINV,  BSET,
      BCLRI, BEXTI, BINVI, BSETI :  begin
        get_opcode = 7'b0010011;
      end
      default : get_opcode = super.get_opcode();
    endcase
  endfunction : get_opcode

  function bit [2:0] get_func3();
    case (instr_name) inside
      BCLR    : get_func3 = 3'b001;
      BCLRI   : get_func3 = 3'b001;
      BEXT    : get_func3 = 3'b101;
      BEXTI   : get_func3 = 3'b101;
      BINV    : get_func3 = 3'b001;
      BINVI   : get_func3 = 3'b001;
      BSET    : get_func3 = 3'b001;
      BSETI   : get_func3 = 3'b001;
      default : get_func3 = super.get_func3();
    endcase
  endfunction : get_func3

  function bit [6:0] get_func7();
    case (instr_name) inside
      BCLR    : get_func7 = 7'b0100100;
      BCLRI   : get_func7 = 7'b0100100;
      BEXT    : get_func7 = 7'b0100100;
      BEXTI   : get_func7 = 7'b0100100;
      BINV    : get_func7 = 7'b0110100;
      BINVI   : get_func7 = 7'b0110100;
      BSET    : get_func7 = 7'b0010100;
      BSETI   : get_func7 = 7'b0010100;
      default : get_func7 = super.get_func7();
    endcase
  endfunction : get_func7

  virtual function string convert2bin(string prefix = "");
    string binary = "";

    case (format) inside
      I_FORMAT : begin
        case (instr_name) inside
          BCLRI, BEXTI, BINVI, BSETI : begin
            binary = $sformatf("%8h", {(get_func7() | (is_rv64() && imm[5])), imm[4:0], rs1,
                                        get_func3(), rd, get_opcode()});
          end
        endcase
      end
      default : begin
        if (binary == "") begin
          return super.convert2bin(prefix);
        end
      end
    endcase
  endfunction : convert2bin

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zbs_extension &&
           (RV32ZBS inside { supported_isa } || RV64ZBS inside { supported_isa }) &&
           instr_name inside {
              BCLR, BEXT, BINV, BSET,
              BCLRI, BEXTI, BINVI, BSETI
            });
  endfunction : is_supported

endclass : riscv_zbs_instr
