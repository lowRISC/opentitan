/*
 * Copyright 2019 Google LLC
 * Copyright 2019 Mellanox Technologies Ltd
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

class riscv_b_instr extends riscv_instr;

  rand riscv_reg_t rs3;
  bit has_rs3 = 1'b0;

  `uvm_object_utils(riscv_b_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void set_rand_mode();
    super.set_rand_mode();
    has_rs3 = 1'b0;
    case (format) inside
      R_FORMAT: begin
        if (instr_name inside {CLZW, CTZW, PCNTW, SEXT_B, SEXT_H, CLZ, CTZ, PCNT, BMATFLIP,
                               CRC32_B, CRC32_H, CRC32_W, CRC32C_B, CRC32C_H, CRC32C_W, CRC32_D,
                               CRC32C_D}) begin
          has_rs2 = 1'b0;
        end
      end
      R4_FORMAT: begin
        has_imm = 1'b0;
        has_rs3 = 1'b1;
      end
      I_FORMAT: begin
        has_rs2 = 1'b0;
        if (instr_name inside {FSRI, FSRIW}) begin
          has_rs3 = 1'b1;
        end
      end
    endcase

  endfunction

  function void pre_randomize();
    super.pre_randomize();
    rs3.rand_mode(has_rs3);
  endfunction


  virtual function void set_imm_len();

    if (format inside {I_FORMAT}) begin
      if (category inside {SHIFT, LOGICAL}) begin
        if (group == RV64B && !(instr_name inside {SLLIU_W})) begin
          imm_len = $clog2(XLEN) - 1;
        end else begin
          imm_len = $clog2(XLEN);
        end
      end

      // ARITHMETIC RV32B
      if (instr_name inside {SHFLI, UNSHFLI}) begin
        imm_len = $clog2(XLEN) - 1;
      end
      // ARITHMETIC RV64B
      if (instr_name inside {ADDIWU}) begin
        imm_len = 12;
      end
    end

    imm_mask = imm_mask << imm_len;
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str_final, asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    case (format)
      I_FORMAT: begin
        if (instr_name inside {FSRI, FSRIW}) begin  // instr rd,rs1,rs3,imm
          asm_str_final = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(),
                                    rs3.name(), get_imm());
        end
      end

      R_FORMAT: begin  //instr rd rs1
        if (!has_rs2) begin
          asm_str_final = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end
      end

      R4_FORMAT: begin  // instr rd,rs1,rs2,rs3
        asm_str_final = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(),
                                  rs2.name(), rs3.name());
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase

    if (asm_str_final == "") begin
      return super.convert2asm(prefix);
    end

    if (comment != "") asm_str_final = {asm_str_final, " #", comment};
    return asm_str_final.tolower();
  endfunction

  function bit [6:0] get_opcode();
    case (instr_name) inside
      ANDN, ORN, XNOR, GORC, SLO, SRO, ROL, ROR, SBCLR, SBSET, SBINV, SBEXT,
          GREV: get_opcode = 7'b0110011;
      SLOI, SROI, RORI, SBCLRI, SBSETI, SBINVI, SBEXTI, GORCI, GREVI, CMIX, CMOV,
          FSL: get_opcode = 7'b0010011;
      FSR, FSRI, CLZ, CTZ, PCNT, BMATFLIP, SEXT_B, SEXT_H, CRC32_B, CRC32_H, CRC32_W, CRC32C_B,
          CRC32C_H: get_opcode = 7'b0010011;
      CRC32C_W, CRC32_D, CRC32C_D: get_opcode = 7'b0010011;
      CLMUL, CLMULR, CLMULH, MIN, MAX, MINU, MAXU, SHFL, UNSHFL, BDEP, BEXT, PACK, PACKU, BMATOR,
          BMATXOR, PACKH, BFP: get_opcode = 7'b0110011;
      SHFLI, UNSHFLI: get_opcode = 7'b0010011;
      ADDIWU, SLLIU_W: get_opcode = 7'b0011011;
      ADDWU, SUBWU, ADDU_W, SUBU_W, SLOW, SROW, ROLW, RORW, SBCLRW, SBSETW, SBINVW, SBEXTW, GORCW,
          GREVW: get_opcode = 7'b0111011;
      SLOIW, SROIW, RORIW, SBCLRIW, SBSETIW, SBINVIW, GORCIW, GREVIW: get_opcode = 7'b0011011;
      FSLW, FSRW: get_opcode = 7'b0111011;
      FSRIW, CLZW, CTZW, PCNTW: get_opcode = 7'b0011011;
      CLMULW, CLMULRW, CLMULHW, SHFLW, UNSHFLW, BDEPW, BEXTW, PACKW, PACKUW,
          BFPW: get_opcode = 7'b0111011;
      default: get_opcode = super.get_opcode();
    endcase
  endfunction

  virtual function bit [2:0] get_func3();
    case (instr_name) inside
      ANDN: get_func3 = 3'b111;
      ORN: get_func3 = 3'b110;
      XNOR: get_func3 = 3'b100;
      GORC: get_func3 = 3'b101;
      SLO: get_func3 = 3'b001;
      SRO: get_func3 = 3'b101;
      ROL: get_func3 = 3'b001;
      ROR: get_func3 = 3'b101;
      SBCLR: get_func3 = 3'b001;
      SBSET: get_func3 = 3'b001;
      SBINV: get_func3 = 3'b001;
      SBEXT: get_func3 = 3'b101;
      GREV: get_func3 = 3'b101;
      SLOI: get_func3 = 3'b001;
      SROI: get_func3 = 3'b101;
      RORI: get_func3 = 3'b101;
      SBCLRI: get_func3 = 3'b001;
      SBSETI: get_func3 = 3'b001;
      SBINVI: get_func3 = 3'b001;
      SBEXTI: get_func3 = 3'b101;
      GORCI: get_func3 = 3'b101;
      GREVI: get_func3 = 3'b101;
      CMIX: get_func3 = 3'b001;
      CMOV: get_func3 = 3'b101;
      FSL: get_func3 = 3'b001;
      FSR: get_func3 = 3'b101;
      FSRI: get_func3 = 3'b101;
      CLZ: get_func3 = 3'b001;
      CTZ: get_func3 = 3'b001;
      PCNT: get_func3 = 3'b001;
      BMATFLIP: get_func3 = 3'b001;
      SEXT_B: get_func3 = 3'b001;
      SEXT_H: get_func3 = 3'b001;
      CRC32_B: get_func3 = 3'b001;
      CRC32_H: get_func3 = 3'b001;
      CRC32_W: get_func3 = 3'b001;
      CRC32C_B: get_func3 = 3'b001;
      CRC32C_H: get_func3 = 3'b001;
      CRC32C_W: get_func3 = 3'b001;
      CRC32_D: get_func3 = 3'b001;
      CRC32C_D: get_func3 = 3'b001;
      CLMUL: get_func3 = 3'b001;
      CLMULR: get_func3 = 3'b010;
      CLMULH: get_func3 = 3'b011;
      MIN: get_func3 = 3'b100;
      MAX: get_func3 = 3'b101;
      MINU: get_func3 = 3'b110;
      MAXU: get_func3 = 3'b111;
      SHFL: get_func3 = 3'b001;
      UNSHFL: get_func3 = 3'b101;
      BDEP: get_func3 = 3'b110;
      BEXT: get_func3 = 3'b110;
      PACK: get_func3 = 3'b100;
      PACKU: get_func3 = 3'b100;
      BMATOR: get_func3 = 3'b011;
      BMATXOR: get_func3 = 3'b011;
      PACKH: get_func3 = 3'b111;
      BFP: get_func3 = 3'b111;
      SHFLI: get_func3 = 3'b001;
      UNSHFLI: get_func3 = 3'b101;
      ADDIWU: get_func3 = 3'b100;
      SLLIU_W: get_func3 = 3'b001;
      ADDWU: get_func3 = 3'b000;
      SUBWU: get_func3 = 3'b000;
      ADDU_W: get_func3 = 3'b000;
      SUBU_W: get_func3 = 3'b000;
      SLOW: get_func3 = 3'b001;
      SROW: get_func3 = 3'b101;
      ROLW: get_func3 = 3'b001;
      RORW: get_func3 = 3'b101;
      SBCLRW: get_func3 = 3'b001;
      SBSETW: get_func3 = 3'b001;
      SBINVW: get_func3 = 3'b001;
      SBEXTW: get_func3 = 3'b101;
      GORCW: get_func3 = 3'b101;
      GREVW: get_func3 = 3'b101;
      SLOIW: get_func3 = 3'b001;
      SROIW: get_func3 = 3'b101;
      RORIW: get_func3 = 3'b101;
      SBCLRIW: get_func3 = 3'b001;
      SBSETIW: get_func3 = 3'b001;
      SBINVIW: get_func3 = 3'b001;
      GORCIW: get_func3 = 3'b101;
      GREVIW: get_func3 = 3'b101;
      FSLW: get_func3 = 3'b001;
      FSRW: get_func3 = 3'b101;
      FSRIW: get_func3 = 3'b101;
      CLZW: get_func3 = 3'b001;
      CTZW: get_func3 = 3'b001;
      PCNTW: get_func3 = 3'b001;
      CLMULW: get_func3 = 3'b001;
      CLMULRW: get_func3 = 3'b010;
      CLMULHW: get_func3 = 3'b011;
      SHFLW: get_func3 = 3'b001;
      UNSHFLW: get_func3 = 3'b101;
      BDEPW: get_func3 = 3'b110;
      BEXTW: get_func3 = 3'b110;
      PACKW: get_func3 = 3'b100;
      PACKUW: get_func3 = 3'b100;
      BFPW: get_func3 = 3'b111;
      default: get_func3 = super.get_func3();
    endcase
    ;
  endfunction

  function bit [6:0] get_func7();
    case (instr_name) inside
      ANDN: get_func7 = 7'b0100000;
      ORN: get_func7 = 7'b0100000;
      XNOR: get_func7 = 7'b0100000;
      GORC: get_func7 = 7'b0010100;
      SLO: get_func7 = 7'b0010000;
      SRO: get_func7 = 7'b0010000;
      ROL: get_func7 = 7'b0110000;
      ROR: get_func7 = 7'b0110000;
      SBCLR: get_func7 = 7'b0100100;
      SBSET: get_func7 = 7'b0010100;
      SBINV: get_func7 = 7'b0110100;
      SBEXT: get_func7 = 7'b0100100;
      GREV: get_func7 = 7'b0110100;
      CLZ: get_func7 = 7'b0110000;
      CTZ: get_func7 = 7'b0110000;
      PCNT: get_func7 = 7'b0110000;
      BMATFLIP: get_func7 = 7'b0110000;
      SEXT_B: get_func7 = 7'b0110000;
      SEXT_H: get_func7 = 7'b0110000;
      CRC32_B: get_func7 = 7'b0110000;
      CRC32_H: get_func7 = 7'b0110000;
      CRC32_W: get_func7 = 7'b0110000;
      CRC32C_B: get_func7 = 7'b0110000;
      CRC32C_H: get_func7 = 7'b0110000;
      CRC32C_W: get_func7 = 7'b0110000;
      CRC32_D: get_func7 = 7'b0110000;
      CRC32C_D: get_func7 = 7'b0110000;
      CLMUL: get_func7 = 7'b0000101;
      CLMULR: get_func7 = 7'b0000101;
      CLMULH: get_func7 = 7'b0000101;
      MIN: get_func7 = 7'b0000101;
      MAX: get_func7 = 7'b0000101;
      MINU: get_func7 = 7'b0000101;
      MAXU: get_func7 = 7'b0000101;
      SHFL: get_func7 = 7'b0000100;
      UNSHFL: get_func7 = 7'b0000100;
      BDEP: get_func7 = 7'b0100100;
      BEXT: get_func7 = 7'b0000100;
      PACK: get_func7 = 7'b0000100;
      PACKU: get_func7 = 7'b0100100;
      BMATOR: get_func7 = 7'b0000100;
      BMATXOR: get_func7 = 7'b0100100;
      PACKH: get_func7 = 7'b0000100;
      BFP: get_func7 = 7'b0100100;
      ADDWU: get_func7 = 7'b0000101;
      SUBWU: get_func7 = 7'b0100101;
      ADDU_W: get_func7 = 7'b0000100;
      SUBU_W: get_func7 = 7'b0100100;
      SLOW: get_func7 = 7'b0010000;
      SROW: get_func7 = 7'b0010000;
      ROLW: get_func7 = 7'b0110000;
      RORW: get_func7 = 7'b0110000;
      SBCLRW: get_func7 = 7'b0100100;
      SBSETW: get_func7 = 7'b0010100;
      SBINVW: get_func7 = 7'b0110100;
      SBEXTW: get_func7 = 7'b0100100;
      GORCW: get_func7 = 7'b0010100;
      GREVW: get_func7 = 7'b0110100;
      SLOIW: get_func7 = 7'b0010000;
      SROIW: get_func7 = 7'b0010000;
      RORIW: get_func7 = 7'b0110000;
      SBCLRIW: get_func7 = 7'b0100100;
      SBSETIW: get_func7 = 7'b0010100;
      SBINVIW: get_func7 = 7'b0110100;
      GORCIW: get_func7 = 7'b0010100;
      GREVIW: get_func7 = 7'b0110100;
      CLZW: get_func7 = 7'b0110000;
      CTZW: get_func7 = 7'b0110000;
      PCNTW: get_func7 = 7'b0110000;
      CLMULW: get_func7 = 7'b0000101;
      CLMULRW: get_func7 = 7'b0000101;
      CLMULHW: get_func7 = 7'b0000101;
      SHFLW: get_func7 = 7'b0000100;
      UNSHFLW: get_func7 = 7'b0000100;
      BDEPW: get_func7 = 7'b0100100;
      BEXTW: get_func7 = 7'b0000100;
      PACKW: get_func7 = 7'b0000100;
      PACKUW: get_func7 = 7'b0100100;
      BFPW: get_func7 = 7'b0100100;
      default: get_func7 = super.get_func7();
    endcase

  endfunction

  function bit [4:0] get_func5();
    case (instr_name) inside
      SLOI: get_func5 = 5'b00100;
      SROI: get_func5 = 5'b00100;
      RORI: get_func5 = 5'b01100;
      SBCLRI: get_func5 = 5'b01001;
      SBSETI: get_func5 = 5'b01001;
      SBINVI: get_func5 = 5'b01101;
      SBEXTI: get_func5 = 5'b01001;
      GORCI: get_func5 = 5'b00101;
      GREVI: get_func5 = 5'b01101;

      CLZW: get_func5 = 5'b00000;
      CTZW: get_func5 = 5'b00001;
      PCNTW: get_func5 = 5'b00010;

      CRC32_B: get_func5 = 5'b10000;
      CRC32_H: get_func5 = 5'b10001;
      CRC32_W: get_func5 = 5'b10010;
      CRC32C_B: get_func5 = 5'b11000;
      CRC32C_H: get_func5 = 5'b11001;
      CRC32C_W: get_func5 = 5'b11010;
      CRC32_D: get_func5 = 5'b10011;
      CRC32C_D: get_func5 = 5'b11011;

      CLZ: get_func5 = 5'b00000;
      CTZ: get_func5 = 5'b00001;
      PCNT: get_func5 = 5'b00010;
      BMATFLIP: get_func5 = 5'b00011;
      SEXT_B: get_func5 = 5'b00100;
      SEXT_H: get_func5 = 5'b00101;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  function bit [1:0] get_func2();
    case (instr_name) inside
      CMIX: get_func2 = 2'b11;
      CMOV: get_func2 = 2'b11;
      FSL: get_func2 = 2'b10;
      FSR: get_func2 = 2'b10;
      FSLW: get_func2 = 2'b10;
      FSRW: get_func2 = 2'b10;
      FSRIW: get_func2 = 2'b10;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary = "";
    case (format)
      R_FORMAT: begin
        if ((category inside {LOGICAL}) && (group == RV32B)) begin
          if (instr_name inside {SEXT_B, SEXT_H}) begin
            binary =
                $sformatf("%8h", {get_func7(), get_func5(), rs1, get_func3(), rd, get_opcode()});
          end
        end

        if ((category inside {ARITHMETIC}) && (group == RV32B)) begin
          if (instr_name inside {CRC32_B, CRC32_H, CRC32_W, CRC32C_B, CRC32C_H, CRC32C_W, CLZ, CTZ,
                                 PCNT}) begin
            binary =
                $sformatf("%8h", {get_func7(), get_func5(), rs1, get_func3(), rd, get_opcode()});
          end
        end

        if ((category inside {ARITHMETIC}) && (group == RV64B)) begin
          if (instr_name inside {CLZW, CTZW, PCNTW, CRC32_D, CRC32C_D, BMATFLIP}) begin
            binary =
                $sformatf("%8h", {get_func7(), get_func5(), rs1, get_func3(), rd, get_opcode()});
          end
        end
      end

      I_FORMAT: begin
        if ((category inside {SHIFT, LOGICAL}) && (group == RV32B)) begin
          binary = $sformatf("%8h", {get_func5(), imm[6:0], rs1, get_func3(), rd, get_opcode()});
        end else if ((category inside {SHIFT, LOGICAL}) && (group == RV64B)) begin
          binary = $sformatf("%8h", {get_func7(), imm[4:0], rs1, get_func3(), rd, get_opcode()});
          if (instr_name == SLLIU_W)
            binary = $sformatf("%8h", {5'b0_0001, imm[6:0], rs1, get_func3(), rd, get_opcode()});
        end

        if (instr_name inside {FSRI}) begin
          binary = $sformatf("%8h", {rs3, 1'b1, imm[5:0], rs1, get_func3(), rd, get_opcode()});
        end

        if ((category inside {ARITHMETIC}) && (group == RV32B)) begin
          binary = $sformatf("%8h", {6'b00_0010, imm[5:0], rs1, get_func3(), rd, get_opcode()});
        end

        if ((category inside {ARITHMETIC}) && (group == RV64B)) begin
          binary = $sformatf("%8h", {imm[11:0], rs1, get_func3(), rd, get_opcode()});
        end
      end

      R4_FORMAT: begin
        binary = $sformatf("%8h", {rs3, get_func2(), rs2, rs1, get_func3(), rd, get_opcode()});
      end
      default: begin
        if (binary == "") binary = super.convert2bin(prefix);
      end
    endcase
    return {prefix, binary};
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_b_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.rs3 = rhs_.rs3;
    this.has_rs3 = rhs_.has_rs3;
  endfunction : do_copy

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return cfg.enable_b_extension && (
           (ZBB inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CLZ, CTZ, CLZW, CTZW, PCNT, PCNTW,
               SLO, SLOI, SLOW, SLOIW,
               SRO, SROI, SROW, SROIW,
               MIN, MINU, MAX, MAXU,
               ADDWU, ADDIWU, SUBWU,
               ADDU_W, SUBU_W,
               SLLIU_W,
               ANDN, ORN,
               XNOR, PACK, PACKW, PACKU, PACKUW, PACKH,
               ROL, ROLW, ROR, RORW, RORI, RORIW
               }) ||
           (ZBS inside {cfg.enable_bitmanip_groups} && instr_name inside {
               SBSET, SBSETW, SBSETI, SBSETIW,
               SBCLR, SBCLRW, SBCLRI, SBCLRIW,
               SBINV, SBINVW, SBINVI, SBINVIW,
               SBEXT, SBEXTW, SBEXTI
               }) ||
           (ZBP inside {cfg.enable_bitmanip_groups} && instr_name inside {
               GREV, GREVW, GREVI, GREVIW,
               GORC, GORCW, GORCI, GORCIW,
               SHFL, SHFLW, UNSHFL, UNSHFLW, SHFLI, UNSHFLI
               }) ||
           (ZBE inside {cfg.enable_bitmanip_groups} && instr_name inside {
               BEXT, BEXTW,
               BDEP, BDEPW
               }) ||
           (ZBF inside {cfg.enable_bitmanip_groups} && instr_name inside {BFP, BFPW}) ||
           (ZBC inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CLMUL, CLMULW, CLMULH, CLMULHW, CLMULR, CLMULRW
               }) ||
           (ZBR inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CRC32_B, CRC32_H, CRC32_W, CRC32_D,
               CRC32C_B, CRC32C_H, CRC32C_W, CRC32C_D
               }) ||
           (ZBM inside {cfg.enable_bitmanip_groups} && instr_name inside {
               BMATOR, BMATXOR, BMATFLIP
               }) ||
           (ZBT inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CMOV, CMIX,
               FSL, FSLW, FSR, FSRW, FSRI, FSRIW}) ||
           // TODO, spec 0.92 doesn't categorize these 2 instr, put them in ZB_TMP #572
           (ZB_TMP inside {cfg.enable_bitmanip_groups} && instr_name inside {
               SEXT_B, SEXT_H})
           );
  endfunction

  // coverage related functons
  virtual function void update_src_regs(string operands[$]);
    // handle special I_FORMAT (FSRI, FSRIW) and R4_FORMAT
    case(format)
      I_FORMAT: begin
        if (instr_name inside {FSRI, FSRIW}) begin
          `DV_CHECK_FATAL(operands.size() == 4, instr_name)
          // fsri rd, rs1, rs3, imm
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          rs3 = get_gpr(operands[2]);
          rs3_value = get_gpr_state(operands[2]);
          get_val(operands[3], imm);
          return;
        end
      end
      R4_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 4)
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        rs2 = get_gpr(operands[2]);
        rs2_value = get_gpr_state(operands[2]);
        rs3 = get_gpr(operands[3]);
        rs3_value = get_gpr_state(operands[3]);
        return;
      end
      default: ;
    endcase
    // reuse base function to handle the other instructions
    super.update_src_regs(operands);
  endfunction : update_src_regs

endclass



