/*
 * Copyright 2019 Google LLC
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

// ---------------------------------------------------------------------------------------------
// This class is used to generate illegal or HINT instructions.
// The illegal instruction will be generated in binary format and mixed with other valid instr.
// The mixed instruction stream will be stored in data section and loaded to instruction pages
// at run time.
// ---------------------------------------------------------------------------------------------

class riscv_illegal_instr extends uvm_object;

  typedef enum bit [2:0] {
    kIllegalOpcode,
    kIllegalFunc3,
    kIllegalFunc7,
    kReservedCompressedInstr,
    kHintInstr
  } illegal_instr_type_e;

  // Default legal opcode for RV32I instructions
  bit [6:0]  legal_opcode[$] = '{7'b0000011,
                                 7'b0001111,
                                 7'b0010011,
                                 7'b0010111,
                                 7'b0100011,
                                 7'b0110111,
                                 7'b1100011,
                                 7'b0110011,
                                 7'b1100111,
                                 7'b1110011,
                                 7'b1101111};

  rand illegal_instr_type_e  exception;
  rand bit [31:0]            instr_bin;
  rand bit [6:0]             opcode;
  rand bit                   compressed;
  rand bit [2:0]             func3;
  rand bit [6:0]             func7;
  rand bit                   has_func3;
  rand bit                   has_func7;
  rand bit [1:0]             c_op;
  rand bit [2:0]             c_msb;
  riscv_instr_gen_config     cfg;

  constraint instr_bit_assignment_c {
    solve opcode before instr_bin;
    solve func3 before instr_bin;
    solve func7 before instr_bin;
    solve c_msb before instr_bin;
    solve c_op before instr_bin;
    if (compressed) {
      instr_bin[1:0] == c_op;
      instr_bin[15:13] == c_msb;
    } else {
      instr_bin[6:0] == opcode;
      if (has_func7) {
        instr_bin[31:25] == func7;
      }
      if (has_func3) {
        instr_bin[14:12] == func3;
      }
    }
  }

  constraint exception_type_c {
    if (compressed) {
      exception inside {kReservedCompressedInstr, kHintInstr};
    } else {
      exception inside {kIllegalOpcode, kIllegalFunc3, kIllegalFunc7};
    }
    if (!has_func7) {
      exception != kIllegalFunc7;
    }
    if (!has_func3) {
      exception != kIllegalFunc3;
    }
  }

  constraint compressed_instr_op_c {
    c_op != 2'b11;
  }

  constraint reserved_compressed_instr_c {
    if (exception == kReservedCompressedInstr) {
      ((instr_bin[15:5] == '0) && (c_op == 2'b00)) ||
      ((c_msb == 3'b100) && (c_op == 2'b00)) ||
      ((instr_bin[15:10] == 6'b100111) && (instr_bin[6:5] == 2'b10) && (c_op == 2'b01)) ||
      ((instr_bin[15:10] == 6'b100111) && (instr_bin[6:5] == 2'b11) && (c_op == 2'b01)) ||
      ((c_msb == 3'b001) && (c_op == 2'b01) && (instr_bin[11:7] == 5'b0) && (XLEN == 64)) ||
      ((c_msb == 3'b011) && (c_op == 2'b01) && (instr_bin[12:2] == 11'h40)) ||
      ((c_msb == 3'b001) && (c_op == 2'b10) && (instr_bin[11:7] == 5'b0)) ||
      ((c_msb == 3'b010) && (c_op == 2'b10) && (instr_bin[11:7] == 5'b0)) ||
      ((c_msb == 3'b011) && (c_op == 2'b10) && (instr_bin[11:7] == 5'b0)) ||
      (instr_bin == 16'b1000_0000_0000_0010);
    }
  }

  constraint hint_instr_c {
    if (exception == kHintInstr) {
      // C.ADDI
      ((c_msb == 3'b000) && (c_op == 2'b01) && ({instr_bin[12], instr_bin[6:2]} == 6'b0)) ||
      // C.LI
      ((c_msb == 3'b010) && (c_op == 2'b01) && (instr_bin[11:7] == 5'b0)) ||
      // C.SRAI64, C.SRLI64
      ((c_msb == 3'b100) && (c_op == 2'b01) && (instr_bin[12:11] == 2'b00) &&
                                               (instr_bin[6:2] == 5'b0)) ||
      // C.LUI
      ((c_msb == 3'b011) && (c_op == 2'b01) && (instr_bin[11:7] == 5'b0) &&
                                               ({instr_bin[12], instr_bin[6:2]} != 6'b0)) ||
      // C.SLLI
      ((c_msb == 3'b000) && (c_op == 2'b10) && (instr_bin[11:7] == 5'b0))  ||
      // C.SLLI64
      ((c_msb == 3'b000) && (c_op == 2'b10) && (instr_bin[11:7] != 5'b0) && !instr_bin[12] &&
                                               (instr_bin[6:2] == 0))  ||
      // C.ADD
      ((c_msb == 3'b100) && (c_op == 2'b10) && (instr_bin[11:7] == 5'b0) && instr_bin[12] &&
                                               (instr_bin[6:2] != 0));
    }
  }

  constraint illegal_opcode_c {
    if (exception == kIllegalOpcode) {
      !(opcode inside {legal_opcode});
      opcode[1:0] == 2'b11;
    } else {
      opcode inside {legal_opcode};
    }
  }

  // TODO: Enable atomic instruction
  constraint no_atomic_c {
    opcode != 7'b0101111;
  }

  constraint illegal_func3_c {
    solve opcode before func3;
    if (!compressed) {
      if (exception == kIllegalFunc3) {
        (opcode == 7'b1100111) -> (func3 != 3'b000);
        (opcode == 7'b1100011) -> (func3 inside {3'b010, 3'b011});

        if (XLEN == 32) {
          (opcode == 7'b0100011) -> (func3 >= 3'b011);
          (opcode == 7'b0000011) -> (func3 inside {3'b011, 3'b111});
        } else {
          (opcode == 7'b0100011) -> (func3 > 3'b011);
          (opcode == 7'b0000011) -> (func3 == 3'b111);
        }
        (opcode == 7'b0001111) -> (!(func3 inside {3'b000, 3'b001}));
        (opcode == 7'b1110011) -> (func3 == 3'b100);
        (opcode == 7'b0011011) -> (!(func3 inside {3'b000, 3'b001, 3'b101}));
        (opcode == 7'b0111011) -> (func3 inside {3'b010, 3'b011});
        opcode inside {7'b1100111, 7'b1100011, 7'b0000011, 7'b0100011,
                       7'b0001111, 7'b1110011, 7'b0011011, 7'b0111011};
      } else {
        (opcode == 7'b1100111) -> (func3 == 3'b000);
        (opcode == 7'b1100011) -> (!(func3 inside {3'b010, 3'b011}));
        if (XLEN == 32) {
          (opcode == 7'b0100011) -> (func3 < 3'b011);
          (opcode == 7'b0000011) -> !(func3 inside {3'b011, 3'b111});
        } else {
          (opcode == 7'b0100011) -> (func3 <= 3'b011);
          (opcode == 7'b0000011) -> (func3 != 3'b111);
        }
        (opcode == 7'b0001111) -> (func3 inside {3'b000, 3'b001});
        (opcode == 7'b1110011) -> (func3 != 3'b100);
        (opcode == 7'b0011011) -> (func3 inside {3'b000, 3'b001, 3'b101});
        (opcode == 7'b0111011) -> (!(func3 inside {3'b010, 3'b011}));
      }
    }
  }

  constraint has_func7_c {
    solve opcode before func7;
    if (((opcode == 7'b0010011) && (func3 inside {3'b001, 3'b101})) ||
        (opcode inside {7'b0110011, 7'b0111011})) {
      has_func7 == 1'b1;
    } else {
      has_func7 == 1'b0;
    }
  }

  constraint has_func3_c {
    solve opcode before func7;
    if ((opcode inside {7'b0110111, 7'b1101111, 7'b0010111})) {
      has_func3 == 1'b0;
    } else {
      has_func3 == 1'b1;
    }
  }

  constraint illegal_func7_c {
    if (!compressed) {
      if (exception == kIllegalFunc7) {
        !(func7 inside {7'b0, 7'b0100000, 7'b1});
      } else {
        func7 inside {7'b0, 7'b0100000, 7'b1};
      }
    }
  }

  `uvm_object_utils(riscv_illegal_instr)
  `uvm_object_new

  function void init(riscv_instr_gen_config cfg);
    this.cfg = cfg;
    if ((riscv_instr_pkg::RV32F inside {riscv_instr_pkg::supported_isa}) ||
         riscv_instr_pkg::RV32D inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0000111, 7'b0100111, 7'b1000011,
                                    7'b1000111, 7'b1001011, 7'b1001111,  7'b1010011};
    end
    if (riscv_instr_pkg::RV64I inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0011011};
    end
    if (riscv_instr_pkg::RV32A inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0101111};
    end
    if ((riscv_instr_pkg::RV64I inside {riscv_instr_pkg::supported_isa}) ||
         riscv_instr_pkg::RV64M inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0111011};
    end
  endfunction

  function string get_bin_str();
    if (compressed) begin
      get_bin_str = $sformatf("%4h", instr_bin[15:0]);
    end else begin
      get_bin_str = $sformatf("%8h", instr_bin[31:0]);
    end
  endfunction

endclass
