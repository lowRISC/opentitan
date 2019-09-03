// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07

/**
 * Traces the executed instructions
 *
 * Note: Verilator does not support the language constructs used in this
 * module!
 */
module ibex_tracer #(
    parameter int unsigned RegAddrWidth = 5
) (
    // Clock and Reset
    input  logic                      clk_i,
    input  logic                      rst_ni,

    input  logic                      fetch_enable_i,
    input  logic [31:0]               hart_id_i,

    input  logic                      valid_i,
    input  logic [31:0]               pc_i,
    input  logic [31:0]               instr_i,
    input  logic [31:0]               rs1_value_i,
    input  logic [31:0]               rs2_value_i,
    input  logic [(RegAddrWidth-1):0] ex_reg_addr_i,
    input  logic [31:0]               ex_reg_wdata_i,
    input  logic [31:0]               ex_data_addr_i,
    input  logic [31:0]               ex_data_wdata_i,
    input  logic [31:0]               ex_data_rdata_i
);

  import ibex_pkg::*;
  import ibex_tracer_pkg::*;

  integer      f;
  string       fn;
  integer      cycles;
  logic [ 4:0] rd, rs1, rs2, rs3;

  typedef struct {
    logic [(RegAddrWidth-1):0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    string       str;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];

    function new ();
      str        = "";
      regs_read  = {};
      regs_write = {};
      mem_access = {};
    endfunction

    function string regAddrToStr(input logic [(RegAddrWidth-1):0] addr);
      begin
        if (addr < 10) begin
          return $sformatf(" x%0d", addr);
        end else begin
          return $sformatf("x%0d", addr);
        end
      end
    endfunction

    function void printInstrTrace();
      mem_acc_t mem_acc;
      begin
        $fwrite(f, "%t %15d %h %h %-36s", simtime,
                                          cycles,
                                          pc_i,
                                          instr_i,
                                          str);

        foreach(regs_write[i]) begin
          if (regs_write[i].addr != 0) begin
            $fwrite(f, " %s=0x%08x", regAddrToStr(regs_write[i].addr), regs_write[i].value);
          end
        end

        foreach(regs_read[i]) begin
          if (regs_read[i].addr != 0) begin
            $fwrite(f, " %s:0x%08x", regAddrToStr(regs_read[i].addr), regs_read[i].value);
          end
        end

        if (mem_access.size() > 0) begin
          mem_acc = mem_access.pop_front();

          $fwrite(f, " PA:0x%08x", mem_acc.addr);

          if (mem_acc.we == 1'b1) begin
            $fwrite(f, " store:0x%08x", mem_acc.wdata);
          end else begin
            $fwrite(f, "  load:0x%08x", mem_acc.rdata);
          end
        end

        $fwrite(f, "\n");
      end
    endfunction

    function void printMnemonic(input string mnemonic);
      begin
        str = mnemonic;
      end
    endfunction // printMnemonic

    function void printRInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value_i});
        regs_read.push_back('{rs2, rs2_value_i});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printRInstr

    function void printIInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value_i});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed({{20 {instr[31]}}, instr[31:20]}));
      end
    endfunction // printIInstr

    function void printIuInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value_i});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, {{20 {instr[31]}}, instr[31:20]});
      end
    endfunction // printIuInstr

    function void printUInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {instr[31:12], 12'h000});
      end
    endfunction // printUInstr

    function void printUJInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed({ {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 }));
      end
    endfunction // printUJInstr

    function void printSBInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value_i});
        regs_read.push_back('{rs2, rs2_value_i});
        str =  $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed({ {19 {instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0 }));
      end
    endfunction // printSBInstr

    function void printCSRInstr(input string mnemonic);
      logic [11:0] csr;
      begin
        csr = instr_i[31:20];

        regs_write.push_back('{rd, 'x});

        if (!instr_i[14]) begin
          regs_read.push_back('{rs1, rs1_value_i});
          str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
        end else begin
          str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, { 27'b0, instr[`REG_S1] }, csr);
        end
      end
    endfunction // printCSRInstr

    function void printLoadInstr();
      string      mnemonic;
      logic [2:0] size;
      mem_acc_t   mem_acc;
      begin
        // detect reg-reg load and find size
        size = instr_i[14:12];
        if (instr_i[14:12] == 3'b111) begin
          size = instr_i[30:28];
        end

        unique case (size)
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b110: mnemonic = "p.elw";
          3'b011,
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
          default: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        regs_write.push_back('{rd, 'x});

        if (instr_i[14:12] != 3'b111) begin
          // regular load
          regs_read.push_back('{rs1, rs1_value_i});
          str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed({{20 {instr[31]}}, instr[31:20]}), rs1);
        end else begin
          printMnemonic("INVALID");
        end

        mem_acc.addr  = ex_data_addr_i;
        mem_acc.rdata = ex_data_rdata_i;
        mem_access.push_back(mem_acc);
      end
    endfunction

    function void printStoreInstr();
      string    mnemonic;
      mem_acc_t mem_acc;
      begin

        unique case (instr_i[13:12])
          2'b00:  mnemonic = "sb";
          2'b01:  mnemonic = "sh";
          2'b10:  mnemonic = "sw";
          2'b11: begin
            printMnemonic("INVALID");
            return;
          end
          default: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        if (!instr_i[14]) begin
          // regular store
          regs_read.push_back('{rs2, rs2_value_i});
          regs_read.push_back('{rs1, rs1_value_i});
          str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed({ {20 {instr[31]}}, instr[31:25], instr[11:7] }), rs1);
        end else begin
          printMnemonic("INVALID");
        end

        mem_acc.addr  = ex_data_addr_i;
        mem_acc.we    = 1'b1;
        mem_acc.wdata = ex_data_wdata_i;
        mem_access.push_back(mem_acc);
      end
    endfunction // printSInstr

  endclass

  mailbox #(instr_trace_t) instr_ex = new ();
  mailbox #(instr_trace_t) instr_wb = new ();

  // cycle counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycles = 0;
    end else begin
      cycles = cycles + 1;
    end
  end

  // open/close output file for writing
  initial begin
    wait(rst_ni == 1'b1);
    wait(fetch_enable_i == 1'b1);
    $sformat(fn, "trace_core_%h.log", hart_id_i);
    $display("[TRACER] Output filename is: %s", fn);
    f = $fopen(fn, "w");
    $fwrite(f, "                Time          Cycles PC       Instr    Mnemonic\n");
  end

  final begin
    $fclose(f);
  end

  assign rd  = instr_i[`REG_D];
  assign rs1 = instr_i[`REG_S1];
  assign rs2 = instr_i[`REG_S2];
  assign rs3 = instr_i[`REG_S3];

  // log execution
  always @(posedge clk_i) begin
    instr_trace_t trace;
    mem_acc_t     mem_acc;
    // special case for WFI because we don't wait for unstalling there
    if (valid_i) begin
      trace = new ();

      trace.simtime    = $time;
      trace.cycles     = cycles;
      trace.pc         = pc_i;
      trace.instr      = instr_i;

      // separate case for 'nop' instruction to avoid overlapping with 'addi'
      if (instr_i == 32'h00_00_00_13) begin
        trace.printMnemonic("nop");
      end else begin
        // use casex instead of case inside due to ModelSim bug
        unique casex (instr_i)
          // Regular opcodes
          INSTR_LUI:        trace.printUInstr("lui");
          INSTR_AUIPC:      trace.printUInstr("auipc");
          INSTR_JAL:        trace.printUJInstr("jal");
          INSTR_JALR:       trace.printIInstr("jalr");
          // BRANCH
          INSTR_BEQ:        trace.printSBInstr("beq");
          INSTR_BNE:        trace.printSBInstr("bne");
          INSTR_BLT:        trace.printSBInstr("blt");
          INSTR_BGE:        trace.printSBInstr("bge");
          INSTR_BLTU:       trace.printSBInstr("bltu");
          INSTR_BGEU:       trace.printSBInstr("bgeu");
          // OPIMM
          INSTR_ADDI:       trace.printIInstr("addi");
          INSTR_SLTI:       trace.printIInstr("slti");
          INSTR_SLTIU:      trace.printIInstr("sltiu");
          INSTR_XORI:       trace.printIInstr("xori");
          INSTR_ORI:        trace.printIInstr("ori");
          INSTR_ANDI:       trace.printIInstr("andi");
          INSTR_SLLI:       trace.printIuInstr("slli");
          INSTR_SRLI:       trace.printIuInstr("srli");
          INSTR_SRAI:       trace.printIuInstr("srai");
          // OP
          INSTR_ADD:        trace.printRInstr("add");
          INSTR_SUB:        trace.printRInstr("sub");
          INSTR_SLL:        trace.printRInstr("sll");
          INSTR_SLT:        trace.printRInstr("slt");
          INSTR_SLTU:       trace.printRInstr("sltu");
          INSTR_XOR:        trace.printRInstr("xor");
          INSTR_SRL:        trace.printRInstr("srl");
          INSTR_SRA:        trace.printRInstr("sra");
          INSTR_OR:         trace.printRInstr("or");
          INSTR_AND:        trace.printRInstr("and");
          // SYSTEM (CSR manipulation)
          INSTR_CSRRW:      trace.printCSRInstr("csrrw");
          INSTR_CSRRS:      trace.printCSRInstr("csrrs");
          INSTR_CSRRC:      trace.printCSRInstr("csrrc");
          INSTR_CSRRWI:     trace.printCSRInstr("csrrwi");
          INSTR_CSRRSI:     trace.printCSRInstr("csrrsi");
          INSTR_CSRRCI:     trace.printCSRInstr("csrrci");
          // SYSTEM (others)
          INSTR_ECALL:      trace.printMnemonic("ecall");
          INSTR_EBREAK:     trace.printMnemonic("ebreak");
          INSTR_MRET:       trace.printMnemonic("mret");
          INSTR_DRET:       trace.printMnemonic("dret");
          INSTR_WFI:        trace.printMnemonic("wfi");
          // RV32M
          INSTR_PMUL:       trace.printRInstr("mul");
          INSTR_PMUH:       trace.printRInstr("mulh");
          INSTR_PMULHSU:    trace.printRInstr("mulhsu");
          INSTR_PMULHU:     trace.printRInstr("mulhu");
          INSTR_DIV:        trace.printRInstr("div");
          INSTR_DIVU:       trace.printRInstr("divu");
          INSTR_REM:        trace.printRInstr("rem");
          INSTR_REMU:       trace.printRInstr("remu");
          // LOAD & STORE
          INSTR_LOAD:       trace.printLoadInstr();
          INSTR_STORE:      trace.printStoreInstr();
          // MISC-MEM
          INSTR_FENCE:      trace.printMnemonic("fence");
          default:          trace.printMnemonic("INVALID");
        endcase // unique case (instr_i)
      end

      // replace register written back
      foreach(trace.regs_write[i]) begin
        if ((trace.regs_write[i].addr == ex_reg_addr_i)) begin
          trace.regs_write[i].value = ex_reg_wdata_i;
        end
      end

      trace.printInstrTrace();
    end
  end // always @ (posedge clk_i)

endmodule

`undef REG_S1
`undef REG_S2
`undef REG_S3
`undef REG_D
