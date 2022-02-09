// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Trace executed instructions in simulation
 *
 * This tracer takes execution information from the RISC-V Verification Interface (RVFI) and
 * produces a text file with a human-readable trace.
 *
 * All traced instructions are written to a log file. By default, the log file is named
 * trace_core_<HARTID>.log, with <HARTID> being the 8 digit hart ID of the core being traced.
 *
 * The file name base, defaulting to "trace_core" can be set using the "ibex_tracer_file_base"
 * plusarg passed to the simulation, e.g. "+ibex_tracer_file_base=ibex_my_trace". The exact syntax
 * of passing plusargs to a simulation depends on the simulator.
 *
 * The creation of the instruction trace is enabled by default but can be disabled for a simulation.
 * This behaviour is controlled by the plusarg "ibex_tracer_enable". Use "ibex_tracer_enable=0" to
 * disable the tracer.
 *
 * The trace contains six columns, separated by tabs:
 * - The simulation time
 * - The clock cycle count since reset
 * - The program counter (PC)
 * - The instruction
 * - The decoded instruction in the same format as objdump, together with the accessed registers and
 *   read/written memory values. Jumps and branches show the target address.
 *   This column may be omitted if the instruction does not decode into a long form.
 * - Accessed registers and memory locations.
 *
 * Significant effort is spent to make the decoding produced by this tracer as similar as possible
 * to the one produced by objdump. This simplifies the correlation between the static program
 * information from the objdump-generated disassembly, and the runtime information from this tracer.
 */
module ibex_tracer (
  input logic        clk_i,
  input logic        rst_ni,

  input logic [31:0] hart_id_i,

  // RVFI as described at https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md
  // The standard interface does not have _i/_o suffixes. For consistency with the standard the
  // signals in this module don't have the suffixes either.
  input logic        rvfi_valid,
  input logic [63:0] rvfi_order,
  input logic [31:0] rvfi_insn,
  input logic        rvfi_trap,
  input logic        rvfi_halt,
  input logic        rvfi_intr,
  input logic [ 1:0] rvfi_mode,
  input logic [ 1:0] rvfi_ixl,
  input logic [ 4:0] rvfi_rs1_addr,
  input logic [ 4:0] rvfi_rs2_addr,
  input logic [ 4:0] rvfi_rs3_addr,
  input logic [31:0] rvfi_rs1_rdata,
  input logic [31:0] rvfi_rs2_rdata,
  input logic [31:0] rvfi_rs3_rdata,
  input logic [ 4:0] rvfi_rd_addr,
  input logic [31:0] rvfi_rd_wdata,
  input logic [31:0] rvfi_pc_rdata,
  input logic [31:0] rvfi_pc_wdata,
  input logic [31:0] rvfi_mem_addr,
  input logic [ 3:0] rvfi_mem_rmask,
  input logic [ 3:0] rvfi_mem_wmask,
  input logic [31:0] rvfi_mem_rdata,
  input logic [31:0] rvfi_mem_wdata
);

  // These signals are part of RVFI, but not used in this module currently.
  // Keep them as part of the interface to change the tracer more easily in the future. Assigning
  // these signals to unused_* signals marks them explicitly as unused, an annotation picked up by
  // linters, including Verilator lint.
  logic [63:0] unused_rvfi_order = rvfi_order;
  logic        unused_rvfi_trap = rvfi_trap;
  logic        unused_rvfi_halt = rvfi_halt;
  logic        unused_rvfi_intr = rvfi_intr;
  logic [ 1:0] unused_rvfi_mode = rvfi_mode;
  logic [ 1:0] unused_rvfi_ixl = rvfi_ixl;

  import ibex_tracer_pkg::*;

  int          file_handle;
  string       file_name;

  int unsigned cycle;
  string       decoded_str;
  logic        insn_is_compressed;

  // Data items accessed during this instruction
  localparam logic [4:0] RS1 = (1 << 0);
  localparam logic [4:0] RS2 = (1 << 1);
  localparam logic [4:0] RS3 = (1 << 2);
  localparam logic [4:0] RD  = (1 << 3);
  localparam logic [4:0] MEM = (1 << 4);
  logic [4:0] data_accessed;

  logic trace_log_enable;
  initial begin
    if ($value$plusargs("ibex_tracer_enable=%b", trace_log_enable)) begin
      if (trace_log_enable == 1'b0) begin
        $display("%m: Instruction trace disabled.");
      end
    end else begin
      trace_log_enable = 1'b1;
    end
  end

  function automatic void printbuffer_dumpline();
    string rvfi_insn_str;

    if (file_handle == 32'h0) begin
      string file_name_base = "trace_core";
      void'($value$plusargs("ibex_tracer_file_base=%s", file_name_base));
      $sformat(file_name, "%s_%h.log", file_name_base, hart_id_i);

      $display("%m: Writing execution trace to %s", file_name);
      file_handle = $fopen(file_name, "w");
      $fwrite(file_handle,
              "Time\tCycle\tPC\tInsn\tDecoded instruction\tRegister and memory contents\n");
    end

    // Write compressed instructions as four hex digits (16 bit word), and
    // uncompressed ones as 8 hex digits (32 bit words).
    if (insn_is_compressed) begin
      rvfi_insn_str = $sformatf("%h", rvfi_insn[15:0]);
    end else begin
      rvfi_insn_str = $sformatf("%h", rvfi_insn);
    end

    $fwrite(file_handle, "%15t\t%d\t%h\t%s\t%s\t",
            $time, cycle, rvfi_pc_rdata, rvfi_insn_str, decoded_str);

    if ((data_accessed & RS1) != 0) begin
      $fwrite(file_handle, " %s:0x%08x", reg_addr_to_str(rvfi_rs1_addr), rvfi_rs1_rdata);
    end
    if ((data_accessed & RS2) != 0) begin
      $fwrite(file_handle, " %s:0x%08x", reg_addr_to_str(rvfi_rs2_addr), rvfi_rs2_rdata);
    end
    if ((data_accessed & RS3) != 0) begin
      $fwrite(file_handle, " %s:0x%08x", reg_addr_to_str(rvfi_rs3_addr), rvfi_rs3_rdata);
    end
    if ((data_accessed & RD) != 0) begin
      $fwrite(file_handle, " %s=0x%08x", reg_addr_to_str(rvfi_rd_addr), rvfi_rd_wdata);
    end
    if ((data_accessed & MEM) != 0) begin
      $fwrite(file_handle, " PA:0x%08x", rvfi_mem_addr);

      if (rvfi_mem_rmask != 4'b0000) begin
        $fwrite(file_handle, " store:0x%08x", rvfi_mem_wdata);
      end
      if (rvfi_mem_wmask != 4'b0000) begin
        $fwrite(file_handle, " load:0x%08x", rvfi_mem_rdata);
      end
    end

    $fwrite(file_handle, "\n");
  endfunction


  // Format register address with "x" prefix, left-aligned to a fixed width of 3 characters.
  function automatic string reg_addr_to_str(input logic [4:0] addr);
    if (addr < 10) begin
      return $sformatf(" x%0d", addr);
    end else begin
      return $sformatf("x%0d", addr);
    end
  endfunction

  // Get a CSR name for a CSR address.
  function automatic string get_csr_name(input logic [11:0] csr_addr);
    unique case (csr_addr)
      12'd0: return "ustatus";
      12'd4: return "uie";
      12'd5: return "utvec";
      12'd64: return "uscratch";
      12'd65: return "uepc";
      12'd66: return "ucause";
      12'd67: return "utval";
      12'd68: return "uip";
      12'd1: return "fflags";
      12'd2: return "frm";
      12'd3: return "fcsr";
      12'd3072: return "cycle";
      12'd3073: return "time";
      12'd3074: return "instret";
      12'd3075: return "hpmcounter3";
      12'd3076: return "hpmcounter4";
      12'd3077: return "hpmcounter5";
      12'd3078: return "hpmcounter6";
      12'd3079: return "hpmcounter7";
      12'd3080: return "hpmcounter8";
      12'd3081: return "hpmcounter9";
      12'd3082: return "hpmcounter10";
      12'd3083: return "hpmcounter11";
      12'd3084: return "hpmcounter12";
      12'd3085: return "hpmcounter13";
      12'd3086: return "hpmcounter14";
      12'd3087: return "hpmcounter15";
      12'd3088: return "hpmcounter16";
      12'd3089: return "hpmcounter17";
      12'd3090: return "hpmcounter18";
      12'd3091: return "hpmcounter19";
      12'd3092: return "hpmcounter20";
      12'd3093: return "hpmcounter21";
      12'd3094: return "hpmcounter22";
      12'd3095: return "hpmcounter23";
      12'd3096: return "hpmcounter24";
      12'd3097: return "hpmcounter25";
      12'd3098: return "hpmcounter26";
      12'd3099: return "hpmcounter27";
      12'd3100: return "hpmcounter28";
      12'd3101: return "hpmcounter29";
      12'd3102: return "hpmcounter30";
      12'd3103: return "hpmcounter31";
      12'd3200: return "cycleh";
      12'd3201: return "timeh";
      12'd3202: return "instreth";
      12'd3203: return "hpmcounter3h";
      12'd3204: return "hpmcounter4h";
      12'd3205: return "hpmcounter5h";
      12'd3206: return "hpmcounter6h";
      12'd3207: return "hpmcounter7h";
      12'd3208: return "hpmcounter8h";
      12'd3209: return "hpmcounter9h";
      12'd3210: return "hpmcounter10h";
      12'd3211: return "hpmcounter11h";
      12'd3212: return "hpmcounter12h";
      12'd3213: return "hpmcounter13h";
      12'd3214: return "hpmcounter14h";
      12'd3215: return "hpmcounter15h";
      12'd3216: return "hpmcounter16h";
      12'd3217: return "hpmcounter17h";
      12'd3218: return "hpmcounter18h";
      12'd3219: return "hpmcounter19h";
      12'd3220: return "hpmcounter20h";
      12'd3221: return "hpmcounter21h";
      12'd3222: return "hpmcounter22h";
      12'd3223: return "hpmcounter23h";
      12'd3224: return "hpmcounter24h";
      12'd3225: return "hpmcounter25h";
      12'd3226: return "hpmcounter26h";
      12'd3227: return "hpmcounter27h";
      12'd3228: return "hpmcounter28h";
      12'd3229: return "hpmcounter29h";
      12'd3230: return "hpmcounter30h";
      12'd3231: return "hpmcounter31h";
      12'd256: return "sstatus";
      12'd258: return "sedeleg";
      12'd259: return "sideleg";
      12'd260: return "sie";
      12'd261: return "stvec";
      12'd262: return "scounteren";
      12'd320: return "sscratch";
      12'd321: return "sepc";
      12'd322: return "scause";
      12'd323: return "stval";
      12'd324: return "sip";
      12'd384: return "satp";
      12'd3857: return "mvendorid";
      12'd3858: return "marchid";
      12'd3859: return "mimpid";
      12'd3860: return "mhartid";
      12'd768: return "mstatus";
      12'd769: return "misa";
      12'd770: return "medeleg";
      12'd771: return "mideleg";
      12'd772: return "mie";
      12'd773: return "mtvec";
      12'd774: return "mcounteren";
      12'd832: return "mscratch";
      12'd833: return "mepc";
      12'd834: return "mcause";
      12'd835: return "mtval";
      12'd836: return "mip";
      12'd928: return "pmpcfg0";
      12'd929: return "pmpcfg1";
      12'd930: return "pmpcfg2";
      12'd931: return "pmpcfg3";
      12'd944: return "pmpaddr0";
      12'd945: return "pmpaddr1";
      12'd946: return "pmpaddr2";
      12'd947: return "pmpaddr3";
      12'd948: return "pmpaddr4";
      12'd949: return "pmpaddr5";
      12'd950: return "pmpaddr6";
      12'd951: return "pmpaddr7";
      12'd952: return "pmpaddr8";
      12'd953: return "pmpaddr9";
      12'd954: return "pmpaddr10";
      12'd955: return "pmpaddr11";
      12'd956: return "pmpaddr12";
      12'd957: return "pmpaddr13";
      12'd958: return "pmpaddr14";
      12'd959: return "pmpaddr15";
      12'd2816: return "mcycle";
      12'd2818: return "minstret";
      12'd2819: return "mhpmcounter3";
      12'd2820: return "mhpmcounter4";
      12'd2821: return "mhpmcounter5";
      12'd2822: return "mhpmcounter6";
      12'd2823: return "mhpmcounter7";
      12'd2824: return "mhpmcounter8";
      12'd2825: return "mhpmcounter9";
      12'd2826: return "mhpmcounter10";
      12'd2827: return "mhpmcounter11";
      12'd2828: return "mhpmcounter12";
      12'd2829: return "mhpmcounter13";
      12'd2830: return "mhpmcounter14";
      12'd2831: return "mhpmcounter15";
      12'd2832: return "mhpmcounter16";
      12'd2833: return "mhpmcounter17";
      12'd2834: return "mhpmcounter18";
      12'd2835: return "mhpmcounter19";
      12'd2836: return "mhpmcounter20";
      12'd2837: return "mhpmcounter21";
      12'd2838: return "mhpmcounter22";
      12'd2839: return "mhpmcounter23";
      12'd2840: return "mhpmcounter24";
      12'd2841: return "mhpmcounter25";
      12'd2842: return "mhpmcounter26";
      12'd2843: return "mhpmcounter27";
      12'd2844: return "mhpmcounter28";
      12'd2845: return "mhpmcounter29";
      12'd2846: return "mhpmcounter30";
      12'd2847: return "mhpmcounter31";
      12'd2944: return "mcycleh";
      12'd2946: return "minstreth";
      12'd2947: return "mhpmcounter3h";
      12'd2948: return "mhpmcounter4h";
      12'd2949: return "mhpmcounter5h";
      12'd2950: return "mhpmcounter6h";
      12'd2951: return "mhpmcounter7h";
      12'd2952: return "mhpmcounter8h";
      12'd2953: return "mhpmcounter9h";
      12'd2954: return "mhpmcounter10h";
      12'd2955: return "mhpmcounter11h";
      12'd2956: return "mhpmcounter12h";
      12'd2957: return "mhpmcounter13h";
      12'd2958: return "mhpmcounter14h";
      12'd2959: return "mhpmcounter15h";
      12'd2960: return "mhpmcounter16h";
      12'd2961: return "mhpmcounter17h";
      12'd2962: return "mhpmcounter18h";
      12'd2963: return "mhpmcounter19h";
      12'd2964: return "mhpmcounter20h";
      12'd2965: return "mhpmcounter21h";
      12'd2966: return "mhpmcounter22h";
      12'd2967: return "mhpmcounter23h";
      12'd2968: return "mhpmcounter24h";
      12'd2969: return "mhpmcounter25h";
      12'd2970: return "mhpmcounter26h";
      12'd2971: return "mhpmcounter27h";
      12'd2972: return "mhpmcounter28h";
      12'd2973: return "mhpmcounter29h";
      12'd2974: return "mhpmcounter30h";
      12'd2975: return "mhpmcounter31h";
      12'd803: return "mhpmevent3";
      12'd804: return "mhpmevent4";
      12'd805: return "mhpmevent5";
      12'd806: return "mhpmevent6";
      12'd807: return "mhpmevent7";
      12'd808: return "mhpmevent8";
      12'd809: return "mhpmevent9";
      12'd810: return "mhpmevent10";
      12'd811: return "mhpmevent11";
      12'd812: return "mhpmevent12";
      12'd813: return "mhpmevent13";
      12'd814: return "mhpmevent14";
      12'd815: return "mhpmevent15";
      12'd816: return "mhpmevent16";
      12'd817: return "mhpmevent17";
      12'd818: return "mhpmevent18";
      12'd819: return "mhpmevent19";
      12'd820: return "mhpmevent20";
      12'd821: return "mhpmevent21";
      12'd822: return "mhpmevent22";
      12'd823: return "mhpmevent23";
      12'd824: return "mhpmevent24";
      12'd825: return "mhpmevent25";
      12'd826: return "mhpmevent26";
      12'd827: return "mhpmevent27";
      12'd828: return "mhpmevent28";
      12'd829: return "mhpmevent29";
      12'd830: return "mhpmevent30";
      12'd831: return "mhpmevent31";
      12'd1952: return "tselect";
      12'd1953: return "tdata1";
      12'd1954: return "tdata2";
      12'd1955: return "tdata3";
      12'd1968: return "dcsr";
      12'd1969: return "dpc";
      12'd1970: return "dscratch";
      12'd512: return "hstatus";
      12'd514: return "hedeleg";
      12'd515: return "hideleg";
      12'd516: return "hie";
      12'd517: return "htvec";
      12'd576: return "hscratch";
      12'd577: return "hepc";
      12'd578: return "hcause";
      12'd579: return "hbadaddr";
      12'd580: return "hip";
      12'd896: return "mbase";
      12'd897: return "mbound";
      12'd898: return "mibase";
      12'd899: return "mibound";
      12'd900: return "mdbase";
      12'd901: return "mdbound";
      12'd800: return "mcountinhibit";
      default: return $sformatf("0x%x", csr_addr);
    endcase
  endfunction

  function automatic void decode_mnemonic(input string mnemonic);
    decoded_str = mnemonic;
  endfunction

  function automatic void decode_r_insn(input string mnemonic);
    data_accessed = RS1 | RS2 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs1_addr,
        rvfi_rs2_addr);
  endfunction

  function automatic void decode_r1_insn(input string mnemonic);
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs1_addr);
  endfunction

  function automatic void decode_r_cmixcmov_insn(input string mnemonic);
    data_accessed = RS1 | RS2 | RS3 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,x%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs2_addr,
        rvfi_rs1_addr, rvfi_rs3_addr);
  endfunction

  function automatic void decode_r_funnelshift_insn(input string mnemonic);
    data_accessed = RS1 | RS2 | RS3 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,x%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs1_addr,
        rvfi_rs3_addr, rvfi_rs2_addr);
  endfunction

  function automatic void decode_i_insn(input string mnemonic);
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,%0d", mnemonic, rvfi_rd_addr, rvfi_rs1_addr,
                    $signed({{20 {rvfi_insn[31]}}, rvfi_insn[31:20]}));
  endfunction

  function automatic void decode_i_shift_insn(input string mnemonic);
    // SLLI, SRLI, SRAI, SROI, SLOI, RORI
    logic [4:0] shamt;
    shamt = {rvfi_insn[24:20]};
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,0x%0x", mnemonic, rvfi_rd_addr, rvfi_rs1_addr, shamt);
  endfunction

  function automatic void decode_i_funnelshift_insn( input string mnemonic);
    // fsri
    logic [5:0] shamt;
    shamt = {rvfi_insn[25:20]};
    data_accessed = RS1 | RS3 | RD;
    decoded_str = $sformatf("%s\tx%0d,x%0d,x%0d,0x%0x", mnemonic, rvfi_rd_addr, rvfi_rs1_addr,
        rvfi_rs3_addr, shamt);
  endfunction

  function automatic void decode_i_jalr_insn(input string mnemonic);
    // JALR
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_rd_addr,
        $signed({{20 {rvfi_insn[31]}}, rvfi_insn[31:20]}), rvfi_rs1_addr);
  endfunction

  function automatic void decode_u_insn(input string mnemonic);
    data_accessed = RD;
    decoded_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_rd_addr, {rvfi_insn[31:12]});
  endfunction

  function automatic void decode_j_insn(input string mnemonic);
    // JAL
    data_accessed = RD;
    decoded_str = $sformatf("%s\tx%0d,%0x", mnemonic, rvfi_rd_addr, rvfi_pc_wdata);
  endfunction

  function automatic void decode_b_insn(input string mnemonic);
    logic [31:0] branch_target;
    logic [31:0] imm;

    // We cannot use rvfi_pc_wdata for conditional jumps.
    imm = $signed({ {19 {rvfi_insn[31]}}, rvfi_insn[31], rvfi_insn[7],
             rvfi_insn[30:25], rvfi_insn[11:8], 1'b0 });
    branch_target = rvfi_pc_rdata + imm;

    data_accessed = RS1 | RS2;
    decoded_str = $sformatf("%s\tx%0d,x%0d,%0x",
                            mnemonic, rvfi_rs1_addr, rvfi_rs2_addr, branch_target);
  endfunction

  function automatic void decode_csr_insn(input string mnemonic);
    logic [11:0] csr;
    string csr_name;
    csr = rvfi_insn[31:20];
    csr_name = get_csr_name(csr);

    data_accessed = RD;

    if (!rvfi_insn[14]) begin
      data_accessed |= RS1;
      decoded_str = $sformatf("%s\tx%0d,%s,x%0d",
                              mnemonic, rvfi_rd_addr, csr_name, rvfi_rs1_addr);
    end else begin
      decoded_str = $sformatf("%s\tx%0d,%s,%0d",
                              mnemonic, rvfi_rd_addr, csr_name, {27'b0, rvfi_insn[19:15]});
    end
  endfunction

  function automatic void decode_cr_insn(input string mnemonic);
    if (rvfi_rs2_addr == 5'b0) begin
      if (rvfi_insn[12] == 1'b1) begin
        // C.JALR
        data_accessed = RS1 | RD;
      end else begin
        // C.JR
        data_accessed = RS1;
      end
      decoded_str = $sformatf("%s\tx%0d", mnemonic, rvfi_rs1_addr);
    end else begin
      data_accessed = RS1 | RS2 | RD; // RS1 == RD
      decoded_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs2_addr);
    end
  endfunction

  function automatic void decode_ci_cli_insn(input string mnemonic);
    logic [5:0] imm;
    imm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_rd_addr, $signed(imm));
  endfunction

  function automatic void decode_ci_caddi_insn(input string mnemonic);
    logic [5:0] nzimm;
    nzimm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_rd_addr, $signed(nzimm));
  endfunction

  function automatic void decode_ci_caddi16sp_insn(input string mnemonic);
    logic [9:0] nzimm;
    nzimm = {rvfi_insn[12], rvfi_insn[4:3], rvfi_insn[5], rvfi_insn[2], rvfi_insn[6], 4'b0};
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_rd_addr, $signed(nzimm));
  endfunction

  function automatic void decode_ci_clui_insn(input string mnemonic);
    logic [5:0] nzimm;
    nzimm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_rd_addr, 20'($signed(nzimm)));
  endfunction

  function automatic void decode_ci_cslli_insn(input string mnemonic);
    logic [5:0] shamt;
    shamt = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_rd_addr, shamt);
  endfunction

  function automatic void decode_ciw_insn(input string mnemonic);
    // C.ADDI4SPN
    logic [9:0] nzuimm;
    nzuimm = {rvfi_insn[10:7], rvfi_insn[12:11], rvfi_insn[5], rvfi_insn[6], 2'b00};
    data_accessed = RD;
    decoded_str = $sformatf("%s\tx%0d,x2,%0d", mnemonic, rvfi_rd_addr, nzuimm);
  endfunction

  function automatic void decode_cb_sr_insn(input string mnemonic);
    logic [5:0] shamt;
    shamt = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RS1 | RD;
    decoded_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_rs1_addr, shamt);
  endfunction

  function automatic void decode_cb_insn(input string mnemonic);
    logic [7:0] imm;
    logic [31:0] jump_target;
    if (rvfi_insn[15:13] == 3'b110 || rvfi_insn[15:13] == 3'b111) begin
      // C.BNEZ and C.BEQZ
      // We cannot use rvfi_pc_wdata for conditional jumps.
      imm = {rvfi_insn[12], rvfi_insn[6:5], rvfi_insn[2], rvfi_insn[11:10], rvfi_insn[4:3]};
      jump_target = rvfi_pc_rdata + 32'($signed({imm, 1'b0}));
      data_accessed = RS1;
      decoded_str = $sformatf("%s\tx%0d,%0x", mnemonic, rvfi_rs1_addr, jump_target);
    end else if (rvfi_insn[15:13] == 3'b100) begin
      // C.ANDI
      imm = {{2{rvfi_insn[12]}}, rvfi_insn[12], rvfi_insn[6:2]};
      data_accessed = RS1 | RD; // RS1 == RD
      decoded_str = $sformatf("%s\tx%0d,%0d", mnemonic, rvfi_rd_addr, $signed(imm));
    end else begin
      imm = {rvfi_insn[12], rvfi_insn[6:2], 2'b00};
      data_accessed = RS1;
      decoded_str = $sformatf("%s\tx%0d,0x%0x", mnemonic, rvfi_rs1_addr, imm);
    end
  endfunction

  function automatic void decode_cs_insn(input string mnemonic);
    data_accessed = RS1 | RS2 | RD; // RS1 == RD
    decoded_str = $sformatf("%s\tx%0d,x%0d", mnemonic, rvfi_rd_addr, rvfi_rs2_addr);
  endfunction

  function automatic void decode_cj_insn(input string mnemonic);
    if (rvfi_insn[15:13] == 3'b001) begin
      // C.JAL
      data_accessed = RD;
    end
    decoded_str = $sformatf("%s\t%0x", mnemonic, rvfi_pc_wdata);
  endfunction

  function automatic void decode_compressed_load_insn(input string mnemonic);
    logic [7:0] imm;

    if (rvfi_insn[1:0] == OPCODE_C0) begin
      // C.LW
      imm = {1'b0, rvfi_insn[5], rvfi_insn[12:10], rvfi_insn[6], 2'b00};
    end else begin
      // C.LWSP
      imm = {rvfi_insn[3:2], rvfi_insn[12], rvfi_insn[6:4], 2'b00};
    end
    data_accessed = RS1 | RD | MEM;
    decoded_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_rd_addr, imm, rvfi_rs1_addr);
  endfunction

  function automatic void decode_compressed_store_insn(input string mnemonic);
    logic [7:0] imm;
    if (rvfi_insn[1:0] == OPCODE_C0) begin
      // C.SW
      imm = {1'b0, rvfi_insn[5], rvfi_insn[12:10], rvfi_insn[6], 2'b00};
    end else begin
      // C.SWSP
      imm = {rvfi_insn[8:7], rvfi_insn[12:9], 2'b00};
    end
    data_accessed = RS1 | RS2 | MEM;
    decoded_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_rs2_addr, imm, rvfi_rs1_addr);
  endfunction

  function automatic void decode_load_insn();
    string      mnemonic;

    /*
    Gives wrong results in Verilator < 4.020.
    See https://github.com/lowRISC/ibex/issues/372 and
    https://www.veripool.org/issues/1536-Verilator-Misoptimization-in-if-and-case-with-default-statement-inside-a-function

    unique case (rvfi_insn[14:12])
      3'b000: mnemonic = "lb";
      3'b001: mnemonic = "lh";
      3'b010: mnemonic = "lw";
      3'b100: mnemonic = "lbu";
      3'b101: mnemonic = "lhu";
      default: begin
        decode_mnemonic("INVALID");
        return;
      end
    endcase
    */
    logic [2:0] size;
    size = rvfi_insn[14:12];
    if (size == 3'b000) begin
      mnemonic = "lb";
    end else if (size == 3'b001) begin
      mnemonic = "lh";
    end else if (size == 3'b010) begin
      mnemonic = "lw";
    end else if (size == 3'b100) begin
      mnemonic = "lbu";
    end else if (size == 3'b101) begin
      mnemonic = "lhu";
    end else begin
      decode_mnemonic("INVALID");
      return;
    end


    data_accessed = RD | RS1 | MEM;
    decoded_str = $sformatf("%s\tx%0d,%0d(x%0d)", mnemonic, rvfi_rd_addr,
                    $signed({{20 {rvfi_insn[31]}}, rvfi_insn[31:20]}), rvfi_rs1_addr);
  endfunction

  function automatic void decode_store_insn();
    string    mnemonic;

    unique case (rvfi_insn[13:12])
      2'b00:  mnemonic = "sb";
      2'b01:  mnemonic = "sh";
      2'b10:  mnemonic = "sw";
      default: begin
        decode_mnemonic("INVALID");
        return;
      end
    endcase

    if (!rvfi_insn[14]) begin
      // regular store
      data_accessed = RS1 | RS2 | MEM;
      decoded_str = $sformatf("%s\tx%0d,%0d(x%0d)",
                              mnemonic,
                              rvfi_rs2_addr,
                              $signed({{20{rvfi_insn[31]}}, rvfi_insn[31:25], rvfi_insn[11:7]}),
                              rvfi_rs1_addr);
    end else begin
      decode_mnemonic("INVALID");
    end
  endfunction

  function automatic string get_fence_description(logic [3:0] bits);
    string desc = "";
    if (bits[3]) begin
      desc = {desc, "i"};
    end
    if (bits[2]) begin
      desc = {desc, "o"};
    end
    if (bits[1]) begin
      desc = {desc, "r"};
    end
    if (bits[0]) begin
      desc = {desc, "w"};
    end
    return desc;
  endfunction

  function automatic void decode_fence();
    string predecessor;
    string successor;
    predecessor = get_fence_description(rvfi_insn[27:24]);
    successor = get_fence_description(rvfi_insn[23:20]);
    decoded_str = $sformatf("fence\t%s,%s", predecessor, successor);
  endfunction

  // cycle counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle <= 0;
    end else begin
      cycle <= cycle + 1;
    end
  end

  // close output file for writing
  final begin
    if (file_handle != 32'h0) begin
      $fclose(file_handle);
    end
  end

  // log execution
  always_ff @(posedge clk_i) begin
    if (rvfi_valid && trace_log_enable) begin
      printbuffer_dumpline();
    end
  end

  always_comb begin
    decoded_str = "";
    data_accessed = 5'h0;
    insn_is_compressed = 0;

    // Check for compressed instructions
    if (rvfi_insn[1:0] != 2'b11) begin
      insn_is_compressed = 1;
      // Separate case to avoid overlapping decoding
      if (rvfi_insn[15:13] == INSN_CMV[15:13] && rvfi_insn[1:0] == OPCODE_C2) begin
        if (rvfi_insn[12] == INSN_CADD[12]) begin
          if (rvfi_insn[11:2] == INSN_CEBREAK[11:2]) begin
            decode_mnemonic("c.ebreak");
          end else if (rvfi_insn[6:2] == INSN_CJALR[6:2]) begin
            decode_cr_insn("c.jalr");
          end else begin
            decode_cr_insn("c.add");
          end
        end else begin
          if (rvfi_insn[6:2] == INSN_CJR[6:2]) begin
            decode_cr_insn("c.jr");
          end else begin
            decode_cr_insn("c.mv");
          end
        end
      end else begin
        unique casez (rvfi_insn[15:0])
          // C0 Opcodes
          INSN_CADDI4SPN: begin
            if (rvfi_insn[12:2] == 11'h0) begin
              // Align with pseudo-mnemonic used by GNU binutils and LLVM's MC layer
              decode_mnemonic("c.unimp");
            end else begin
              decode_ciw_insn("c.addi4spn");
            end
          end
          INSN_CLW:        decode_compressed_load_insn("c.lw");
          INSN_CSW:        decode_compressed_store_insn("c.sw");
          // C1 Opcodes
          INSN_CADDI:      decode_ci_caddi_insn("c.addi");
          INSN_CJAL:       decode_cj_insn("c.jal");
          INSN_CJ:         decode_cj_insn("c.j");
          INSN_CLI:        decode_ci_cli_insn("c.li");
          INSN_CLUI: begin
            // These two instructions share opcode
            if (rvfi_insn[11:7] == 5'd2) begin
              decode_ci_caddi16sp_insn("c.addi16sp");
            end else begin
              decode_ci_clui_insn("c.lui");
            end
          end
          INSN_CSRLI:      decode_cb_sr_insn("c.srli");
          INSN_CSRAI:      decode_cb_sr_insn("c.srai");
          INSN_CANDI:      decode_cb_insn("c.andi");
          INSN_CSUB:       decode_cs_insn("c.sub");
          INSN_CXOR:       decode_cs_insn("c.xor");
          INSN_COR:        decode_cs_insn("c.or");
          INSN_CAND:       decode_cs_insn("c.and");
          INSN_CBEQZ:      decode_cb_insn("c.beqz");
          INSN_CBNEZ:      decode_cb_insn("c.bnez");
          // C2 Opcodes
          INSN_CSLLI:      decode_ci_cslli_insn("c.slli");
          INSN_CLWSP:      decode_compressed_load_insn("c.lwsp");
          INSN_SWSP:       decode_compressed_store_insn("c.swsp");
          default:         decode_mnemonic("INVALID");
        endcase
      end
    end else begin
      unique casez (rvfi_insn)
        // Regular opcodes
        INSN_LUI:        decode_u_insn("lui");
        INSN_AUIPC:      decode_u_insn("auipc");
        INSN_JAL:        decode_j_insn("jal");
        INSN_JALR:       decode_i_jalr_insn("jalr");
        // BRANCH
        INSN_BEQ:        decode_b_insn("beq");
        INSN_BNE:        decode_b_insn("bne");
        INSN_BLT:        decode_b_insn("blt");
        INSN_BGE:        decode_b_insn("bge");
        INSN_BLTU:       decode_b_insn("bltu");
        INSN_BGEU:       decode_b_insn("bgeu");
        // OPIMM
        INSN_ADDI: begin
          if (rvfi_insn == 32'h00_00_00_13) begin
            // TODO: objdump doesn't decode this as nop currently, even though it would be helpful
            // Decide what to do here: diverge from objdump, or make the trace less readable to
            // users.
            //decode_mnemonic("nop");
            decode_i_insn("addi");
          end else begin
            decode_i_insn("addi");
          end
        end
        INSN_SLTI:       decode_i_insn("slti");
        INSN_SLTIU:      decode_i_insn("sltiu");
        INSN_XORI:       decode_i_insn("xori");
        INSN_ORI:        decode_i_insn("ori");
        // Unlike the ratified v.1.0.0 bitmanip extension, the v.0.94 draft extension continues to
        // define the pseudo-instruction
        //   zext.b rd rs = andi rd, rs, 255.
        // However, for now the tracer doesn't emit this due to a lack of support in the LLVM and
        // GCC toolchains. Enabling this functionality when the time is right is tracked in
        // https://github.com/lowRISC/ibex/issues/1228
        INSN_ANDI:       decode_i_insn("andi");
        // INSN_ANDI:begin
          // casez (rvfi_insn)
            // INSN_ZEXTB:  decode_r1_insn("zext.b");
            // default:     decode_i_insn("andi");
          // endcase
        // end
        INSN_SLLI:       decode_i_shift_insn("slli");
        INSN_SRLI:       decode_i_shift_insn("srli");
        INSN_SRAI:       decode_i_shift_insn("srai");
        // OP
        INSN_ADD:        decode_r_insn("add");
        INSN_SUB:        decode_r_insn("sub");
        INSN_SLL:        decode_r_insn("sll");
        INSN_SLT:        decode_r_insn("slt");
        INSN_SLTU:       decode_r_insn("sltu");
        INSN_XOR:        decode_r_insn("xor");
        INSN_SRL:        decode_r_insn("srl");
        INSN_SRA:        decode_r_insn("sra");
        INSN_OR:         decode_r_insn("or");
        INSN_AND:        decode_r_insn("and");
        // SYSTEM (CSR manipulation)
        INSN_CSRRW:      decode_csr_insn("csrrw");
        INSN_CSRRS:      decode_csr_insn("csrrs");
        INSN_CSRRC:      decode_csr_insn("csrrc");
        INSN_CSRRWI:     decode_csr_insn("csrrwi");
        INSN_CSRRSI:     decode_csr_insn("csrrsi");
        INSN_CSRRCI:     decode_csr_insn("csrrci");
        // SYSTEM (others)
        INSN_ECALL:      decode_mnemonic("ecall");
        INSN_EBREAK:     decode_mnemonic("ebreak");
        INSN_MRET:       decode_mnemonic("mret");
        INSN_DRET:       decode_mnemonic("dret");
        INSN_WFI:        decode_mnemonic("wfi");
        // RV32M
        INSN_PMUL:       decode_r_insn("mul");
        INSN_PMUH:       decode_r_insn("mulh");
        INSN_PMULHSU:    decode_r_insn("mulhsu");
        INSN_PMULHU:     decode_r_insn("mulhu");
        INSN_DIV:        decode_r_insn("div");
        INSN_DIVU:       decode_r_insn("divu");
        INSN_REM:        decode_r_insn("rem");
        INSN_REMU:       decode_r_insn("remu");
        // LOAD & STORE
        INSN_LOAD:       decode_load_insn();
        INSN_STORE:      decode_store_insn();
        // MISC-MEM
        INSN_FENCE:      decode_fence();
        INSN_FENCEI:     decode_mnemonic("fence.i");
        // RV32B - ZBA
        INSN_SH1ADD:     decode_r_insn("sh1add");
        INSN_SH2ADD:     decode_r_insn("sh2add");
        INSN_SH3ADD:     decode_r_insn("sh3add");
        // RV32B - ZBB
        INSN_RORI:       decode_i_shift_insn("rori");
        INSN_ROL:        decode_r_insn("rol");
        INSN_ROR:        decode_r_insn("ror");
        INSN_MIN:        decode_r_insn("min");
        INSN_MAX:        decode_r_insn("max");
        INSN_MINU:       decode_r_insn("minu");
        INSN_MAXU:       decode_r_insn("maxu");
        INSN_XNOR:       decode_r_insn("xnor");
        INSN_ORN:        decode_r_insn("orn");
        INSN_ANDN:       decode_r_insn("andn");
        // The ratified v.1.0.0 bitmanip extension defines the pseudo-instruction
        //   zext.h rd rs = pack rd, rs, zero.
        // However, for now the tracer doesn't emit this due to a lack of support in the LLVM and
        // GCC toolchains. Enabling this functionality when the time is right is tracked in
        // https://github.com/lowRISC/ibex/issues/1228
        INSN_PACK:       decode_r_insn("pack");
        // INSN_PACK: begin
          // casez (rvfi_insn)
            // INSN_ZEXTH:  decode_r1_insn("zext.h");
            // default:     decode_r_insn("pack");
          // endcase
        // end
        INSN_PACKH:      decode_r_insn("packh");
        INSN_PACKU:      decode_r_insn("packu");
        INSN_CLZ:        decode_r1_insn("clz");
        INSN_CTZ:        decode_r1_insn("ctz");
        INSN_CPOP:       decode_r1_insn("cpop");
        INSN_SEXTB:      decode_r1_insn("sext.b");
        INSN_SEXTH:      decode_r1_insn("sext.h");
        // RV32B - ZBS
        INSN_BCLRI:     decode_i_insn("bclri");
        INSN_BSETI:     decode_i_insn("bseti");
        INSN_BINVI:     decode_i_insn("binvi");
        INSN_BEXTI:     decode_i_insn("bexti");
        INSN_BCLR:      decode_r_insn("bclr");
        INSN_BSET:      decode_r_insn("bset");
        INSN_BINV:      decode_r_insn("binv");
        INSN_BEXT:      decode_r_insn("bext");
        // RV32B - ZBE
        INSN_BDECOMPRESS: decode_r_insn("bdecompress");
        INSN_BCOMPRESS:   decode_r_insn("bcompress");
        // RV32B - ZBP
        INSN_GREV:       decode_r_insn("grev");
        INSN_GREVI: begin
          unique casez (rvfi_insn)
            INSN_REV_P:  decode_r1_insn("rev.p");
            INSN_REV2_N: decode_r1_insn("rev2.n");
            INSN_REV_N:  decode_r1_insn("rev.n");
            INSN_REV4_B: decode_r1_insn("rev4.b");
            INSN_REV2_B: decode_r1_insn("rev2.b");
            INSN_REV_B:  decode_r1_insn("rev.b");
            INSN_REV8_H: decode_r1_insn("rev8.h");
            INSN_REV4_H: decode_r1_insn("rev4.h");
            INSN_REV2_H: decode_r1_insn("rev2.h");
            INSN_REV_H:  decode_r1_insn("rev.h");
            INSN_REV16:  decode_r1_insn("rev16");
            INSN_REV8:   decode_r1_insn("rev8");
            INSN_REV4:   decode_r1_insn("rev4");
            INSN_REV2:   decode_r1_insn("rev2");
            INSN_REV:    decode_r1_insn("rev");
            default:     decode_i_insn("grevi");
          endcase
        end
        INSN_GORC:       decode_r_insn("gorc");
        INSN_GORCI: begin
          unique casez (rvfi_insn)
            INSN_ORC_P:  decode_r1_insn("orc.p");
            INSN_ORC2_N: decode_r1_insn("orc2.n");
            INSN_ORC_N:  decode_r1_insn("orc.n");
            INSN_ORC4_B: decode_r1_insn("orc4.b");
            INSN_ORC2_B: decode_r1_insn("orc2.b");
            INSN_ORC_B:  decode_r1_insn("orc.b");
            INSN_ORC8_H: decode_r1_insn("orc8.h");
            INSN_ORC4_H: decode_r1_insn("orc4.h");
            INSN_ORC2_H: decode_r1_insn("orc2.h");
            INSN_ORC_H:  decode_r1_insn("orc.h");
            INSN_ORC16:  decode_r1_insn("orc16");
            INSN_ORC8:   decode_r1_insn("orc8");
            INSN_ORC4:   decode_r1_insn("orc4");
            INSN_ORC2:   decode_r1_insn("orc2");
            INSN_ORC:    decode_r1_insn("orc");
            default:     decode_i_insn("gorci");
          endcase
        end
        INSN_SHFL:       decode_r_insn("shfl");
        INSN_SHFLI: begin
          unique casez (rvfi_insn)
            INSN_ZIP_N:  decode_r1_insn("zip.n");
            INSN_ZIP2_B: decode_r1_insn("zip2.b");
            INSN_ZIP_B:  decode_r1_insn("zip.b");
            INSN_ZIP4_H: decode_r1_insn("zip4.h");
            INSN_ZIP2_H: decode_r1_insn("zip2.h");
            INSN_ZIP_H:  decode_r1_insn("zip.h");
            INSN_ZIP8:   decode_r1_insn("zip8");
            INSN_ZIP4:   decode_r1_insn("zip4");
            INSN_ZIP2:   decode_r1_insn("zip2");
            INSN_ZIP:    decode_r1_insn("zip");
            default:     decode_i_insn("shfli");
          endcase
        end
        INSN_UNSHFL:       decode_r_insn("unshfl");
        INSN_UNSHFLI: begin
          unique casez (rvfi_insn)
            INSN_UNZIP_N:  decode_r1_insn("unzip.n");
            INSN_UNZIP2_B: decode_r1_insn("unzip2.b");
            INSN_UNZIP_B:  decode_r1_insn("unzip.b");
            INSN_UNZIP4_H: decode_r1_insn("unzip4.h");
            INSN_UNZIP2_H: decode_r1_insn("unzip2.h");
            INSN_UNZIP_H:  decode_r1_insn("unzip.h");
            INSN_UNZIP8:   decode_r1_insn("unzip8");
            INSN_UNZIP4:   decode_r1_insn("unzip4");
            INSN_UNZIP2:   decode_r1_insn("unzip2");
            INSN_UNZIP:    decode_r1_insn("unzip");
            default:       decode_i_insn("unshfli");
          endcase
        end
        INSN_XPERM_N:    decode_r_insn("xperm_n");
        INSN_XPERM_B:    decode_r_insn("xperm_b");
        INSN_XPERM_H:    decode_r_insn("xperm_h");
        INSN_SLO:        decode_r_insn("slo");
        INSN_SRO:        decode_r_insn("sro");
        INSN_SLOI:       decode_i_shift_insn("sloi");
        INSN_SROI:       decode_i_shift_insn("sroi");

        // RV32B - ZBT
        INSN_CMIX:       decode_r_cmixcmov_insn("cmix");
        INSN_CMOV:       decode_r_cmixcmov_insn("cmov");
        INSN_FSR:        decode_r_funnelshift_insn("fsr");
        INSN_FSL:        decode_r_funnelshift_insn("fsl");
        INSN_FSRI:       decode_i_funnelshift_insn("fsri");

        // RV32B - ZBF
        INSN_BFP:        decode_r_insn("bfp");

        // RV32B - ZBC
        INSN_CLMUL:      decode_r_insn("clmul");
        INSN_CLMULR:     decode_r_insn("clmulr");
        INSN_CLMULH:     decode_r_insn("clmulh");

        // RV32B - ZBR
        INSN_CRC32_B:    decode_r1_insn("crc32.b");
        INSN_CRC32_H:    decode_r1_insn("crc32.h");
        INSN_CRC32_W:    decode_r1_insn("crc32.w");
        INSN_CRC32C_B:   decode_r1_insn("crc32c.b");
        INSN_CRC32C_H:   decode_r1_insn("crc32c.h");
        INSN_CRC32C_W:   decode_r1_insn("crc32c.w");

        default:         decode_mnemonic("INVALID");
      endcase
    end
  end

endmodule
