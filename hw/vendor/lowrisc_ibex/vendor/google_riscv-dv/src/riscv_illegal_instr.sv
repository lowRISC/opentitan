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

  string comment;

  typedef enum bit [2:0] {
    kIllegalOpcode,
    kIllegalCompressedOpcode,
    kIllegalFunc3,
    kIllegalFunc7,
    kReservedCompressedInstr,
    kHintInstr,
    kIllegalSystemInstr
  } illegal_instr_type_e;

  typedef enum bit [3:0] {
    kIllegalCompressed,
    kReservedAddispn,
    kReservedAddiw,
    kReservedAddi16sp,
    kReservedLui,
    kReservedLwsp,
    kReservedLdsp,
    kReservedLqsp,
    kReservedJr,
    kReservedC0,
    kReservedC1,
    kReservedC2
  } reserved_c_instr_e;

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

   // Default legal opcode for RV32C instructions
  bit [2:0]  legal_c00_opcode[$] = '{3'b000,
                                     3'b010,
                                     3'b110};
  bit [2:0]  legal_c10_opcode[$] = '{3'b000,
                                     3'b010,
                                     3'b100,
                                     3'b110};

  rand illegal_instr_type_e  exception;
  rand reserved_c_instr_e    reserved_c;
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
  privileged_reg_t           csrs[$];

  constraint exception_dist_c {
    exception dist {
      kIllegalOpcode           := 3,
      kIllegalCompressedOpcode := 1,
      kIllegalFunc3            := 1,
      kIllegalFunc7            := 1,
      kReservedCompressedInstr := 1,
      kHintInstr               := 3,
      kIllegalSystemInstr      := 3
    };
    if (!(RV32C inside {supported_isa})) {
      exception != kHintInstr;
      compressed == 1'b0;
    }
  }

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

  // Invalid SYSTEM instructions
  constraint system_instr_c {
    if (exception == kIllegalSystemInstr) {
      opcode == 7'b1110011;
      // ECALL/EBREAK/xRET/WFI
      if (func3 == 3'b000) {
        // Constrain RS1 and RD to be non-zero
        instr_bin[19:15] != 0;
        instr_bin[11:7] != 0;
        // Valid SYSTEM instructions considered by this
        // Constrain the upper 12 bits to be invalid
        !(instr_bin[31:20] inside {12'h0, 12'h1, 12'h2, 12'h102, 12'h302, 12'h7b2, 12'h105});
      } else {
        // Invalid CSR instructions
        !(instr_bin[31:20] inside {csrs});
        !(instr_bin[31:20] inside {custom_csr});
      }
    }
  }

  constraint legal_rv32_c_slli {
    if ((c_msb == 3'b000) && (c_op == 2'b10) && (XLEN == 32)) {
      if (exception == kReservedCompressedInstr) {
        instr_bin[12] == 1;
      } else {
        instr_bin[12] == 0;
      }
    }
  }

  constraint exception_type_c {
    if (compressed) {
      exception inside {kReservedCompressedInstr, kIllegalCompressedOpcode, kHintInstr};
    } else {
      exception inside {kIllegalOpcode, kIllegalFunc3, kIllegalFunc7, kIllegalSystemInstr};
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

  // Avoid generating illegal func3/func7 errors for opcode used by B-extension for now
  //
  // TODO(udi): add support for generating illegal B-extension instructions
  constraint b_extension_c {
    if (RV32B inside {supported_isa}) {
      if (exception inside {kIllegalFunc3, kIllegalFunc7}) {
        !(opcode inside {7'b0110011, 7'b0010011, 7'b0111011});
      }
    }
  }

  constraint zba_extension_c {
    if (RV32ZBA inside {supported_isa}) {
      if (exception inside {kIllegalFunc3, kIllegalFunc7}) {
        !(opcode inside {7'b0110011, 7'b0111011, 7'b0011011});
      }
    }
  }

  constraint zbb_extension_c {
    if (RV32ZBB inside {supported_isa}) {
      if (exception inside {kIllegalFunc3, kIllegalFunc7}) {
        !(opcode inside {7'b0110011, 7'b0010011, 7'b0111011, 7'b0011011});
      }
    }
  }

  constraint zbc_extension_c {
    if (RV32ZBB inside {supported_isa}) {
      if (exception inside {kIllegalFunc3, kIllegalFunc7}) {
        !(opcode inside {7'b0110011});
      }
    }
  }

  constraint zbs_extension_c {
    if (RV32ZBS inside {supported_isa}) {
      if (exception inside {kIllegalFunc3, kIllegalFunc7}) {
        !(opcode inside {7'b0110011, 7'b0010011});
      }
    }
  }

  constraint illegal_compressed_op_c {
    if (exception == kIllegalCompressedOpcode) {
      c_op != 2'b01;
      if (legal_c00_opcode.size() == 8) {
        c_op != 2'b00;
      } else {
        !(c_msb inside {legal_c00_opcode});
      }
      if (legal_c10_opcode.size() == 8) {
        c_op != 2'b10;
      } else {
        !(c_msb inside {legal_c10_opcode});
      }
    }
  }

  constraint reserved_compressed_instr_c {
    solve exception  before reserved_c;
    solve exception  before opcode;
    solve reserved_c before instr_bin;
    solve reserved_c before c_msb;
    solve reserved_c before c_op;
    if (XLEN == 32) {
      //c.addiw is RV64/RV128 only instruction, the encoding is used for C.JAL for RV32C
      reserved_c != kReservedAddiw;
    }
    if (exception == kReservedCompressedInstr) {
      (reserved_c == kIllegalCompressed) -> (instr_bin[15:0] == 0);
      (reserved_c == kReservedAddispn)   -> ((instr_bin[15:5] == '0) && (c_op == 2'b00));
      (reserved_c == kReservedAddiw)     -> ((c_msb == 3'b001) && (c_op == 2'b01) &&
                                             (instr_bin[11:7] == 5'b0));
      (reserved_c == kReservedC0)        -> ((instr_bin[15:10] == 6'b100111) &&
                                             (instr_bin[6:5] == 2'b10) && (c_op == 2'b01));
      (reserved_c == kReservedC1)        -> ((instr_bin[15:10] == 6'b100111) &&
                                             (instr_bin[6:5] == 2'b11) && (c_op == 2'b01));
      (reserved_c == kReservedC2)        -> ((c_msb == 3'b100) && (c_op == 2'b00));
      (reserved_c == kReservedAddi16sp)  -> ((c_msb == 3'b011) && (c_op == 2'b01) &&
                                             (instr_bin[11:7] == 2) &&
                                             !instr_bin[12] && (instr_bin[6:2] == 0));
      (reserved_c == kReservedLui)       -> ((c_msb == 3'b011) && (c_op == 2'b01) &&
                                             !instr_bin[12] && (instr_bin[6:2] == 0));
      (reserved_c == kReservedJr)        -> (instr_bin == 16'b1000_0000_0000_0010);
      (reserved_c == kReservedLqsp)      -> ((c_msb == 3'b001) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
      (reserved_c == kReservedLwsp)      -> ((c_msb == 3'b010) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
      (reserved_c == kReservedLdsp)      -> ((c_msb == 3'b011) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
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
      // C.MV
      ((c_msb == 3'b100) && (c_op == 2'b10) && (instr_bin[11:7] == 0) &&
                                               (instr_bin[6:2]  != 0)) ||
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
    solve opcode before instr_bin;
    if (exception == kIllegalOpcode) {
      !(opcode inside {legal_opcode});
      opcode[1:0] == 2'b11;
    } else {
      opcode inside {legal_opcode};
    }
  }

  // TODO: Enable atomic instruction
  constraint no_atomic_c {
    if (exception != kIllegalOpcode) {
      opcode != 7'b0101111;
    }
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
        !(func7 inside {7'd0, 7'b0100000, 7'd1});
        if (opcode == 7'b0001001) { // SLLI, SRLI, SRAI
          !(func7[6:1] inside {6'd0, 6'b010000});
        }
      } else {
        func7 inside {7'd0, 7'b0100000, 7'd1};
      }
    }
  }

  `uvm_object_utils(riscv_illegal_instr)
  `uvm_object_new

  function void init(riscv_instr_gen_config cfg);
    privileged_reg_t csr;
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
    if (riscv_instr_pkg::RV64I inside {riscv_instr_pkg::supported_isa} ||
        riscv_instr_pkg::RV64M inside {riscv_instr_pkg::supported_isa}) begin
      legal_opcode = {legal_opcode, 7'b0111011};
    end
    if (riscv_instr_pkg::RV64I inside {riscv_instr_pkg::supported_isa}) begin
      legal_c00_opcode = {legal_c00_opcode, 3'b011, 3'b111};
      legal_c10_opcode = {legal_c10_opcode, 3'b011, 3'b111};
    end
    csr = csr.first();
    for (int i = 0; i < csr.num(); i = i + 1) begin
      csrs.push_back(csr);
      csr = csr.next();
    end
  endfunction

  function string get_bin_str();
    if (compressed) begin
      get_bin_str = $sformatf("%4h", instr_bin[15:0]);
    end else begin
      get_bin_str = $sformatf("%8h", instr_bin[31:0]);
    end
    `uvm_info(`gfn, $sformatf("Illegal instruction type: %0s, illegal instruction: 0x%0x",
                               exception.name(), instr_bin), UVM_HIGH)
  endfunction

  function void post_randomize();
    comment = exception.name();
    if (exception == kReservedCompressedInstr) begin
      comment = {comment, " ", reserved_c.name()};
    end else if (exception == kIllegalOpcode) begin
      comment = {comment, " ", $sformatf("%7b", opcode)};
    end
  endfunction

endclass
