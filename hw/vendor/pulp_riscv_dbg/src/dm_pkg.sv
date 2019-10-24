/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Debug-module package, contains common system definitions.
 *
 */

package dm;
  localparam logic [3:0] DbgVersion013 = 4'h2;
  // size of program buffer in junks of 32-bit words
  localparam logic [4:0] ProgBufSize   = 5'h8;

  // amount of data count registers implemented
  localparam logic [3:0] DataCount     = 4'h2;

  // address to which a hart should jump when it was requested to halt
  localparam logic [63:0] HaltAddress = 64'h800;
  localparam logic [63:0] ResumeAddress = HaltAddress + 4;
  localparam logic [63:0] ExceptionAddress = HaltAddress + 8;

  // address where data0-15 is shadowed or if shadowed in a CSR
  // address of the first CSR used for shadowing the data
  localparam logic [11:0] DataAddr = 12'h380; // we are aligned with Rocket here

  // debug registers
  typedef enum logic [7:0] {
    Data0        = 8'h04,
    Data1        = 8'h05,
    Data2        = 8'h06,
    Data3        = 8'h07,
    Data4        = 8'h08,
    Data5        = 8'h09,
    Data6        = 8'h0A,
    Data7        = 8'h0B,
    Data8        = 8'h0C,
    Data9        = 8'h0D,
    Data10       = 8'h0E,
    Data11       = 8'h0F,
    DMControl    = 8'h10,
    DMStatus     = 8'h11, // r/o
    Hartinfo     = 8'h12,
    HaltSum1     = 8'h13,
    HAWindowSel  = 8'h14,
    HAWindow     = 8'h15,
    AbstractCS   = 8'h16,
    Command      = 8'h17,
    AbstractAuto = 8'h18,
    DevTreeAddr0 = 8'h19,
    DevTreeAddr1 = 8'h1A,
    DevTreeAddr2 = 8'h1B,
    DevTreeAddr3 = 8'h1C,
    NextDM       = 8'h1D,
    ProgBuf0     = 8'h20,
    ProgBuf15    = 8'h2F,
    AuthData     = 8'h30,
    HaltSum2     = 8'h34,
    HaltSum3     = 8'h35,
    SBAddress3   = 8'h37,
    SBCS         = 8'h38,
    SBAddress0   = 8'h39,
    SBAddress1   = 8'h3A,
    SBAddress2   = 8'h3B,
    SBData0      = 8'h3C,
    SBData1      = 8'h3D,
    SBData2      = 8'h3E,
    SBData3      = 8'h3F,
    HaltSum0     = 8'h40
  } dm_csr_e;

  // debug causes
  localparam logic [2:0] CauseBreakpoint = 3'h1;
  localparam logic [2:0] CauseTrigger    = 3'h2;
  localparam logic [2:0] CauseRequest    = 3'h3;
  localparam logic [2:0] CauseSingleStep = 3'h4;

  typedef struct packed {
    logic [31:23] zero1;
    logic         impebreak;
    logic [21:20] zero0;
    logic         allhavereset;
    logic         anyhavereset;
    logic         allresumeack;
    logic         anyresumeack;
    logic         allnonexistent;
    logic         anynonexistent;
    logic         allunavail;
    logic         anyunavail;
    logic         allrunning;
    logic         anyrunning;
    logic         allhalted;
    logic         anyhalted;
    logic         authenticated;
    logic         authbusy;
    logic         hasresethaltreq;
    logic         devtreevalid;
    logic [3:0]   version;
  } dmstatus_t;

  typedef struct packed {
    logic         haltreq;
    logic         resumereq;
    logic         hartreset;
    logic         ackhavereset;
    logic         zero1;
    logic         hasel;
    logic [25:16] hartsello;
    logic [15:6]  hartselhi;
    logic [5:4]   zero0;
    logic         setresethaltreq;
    logic         clrresethaltreq;
    logic         ndmreset;
    logic         dmactive;
  } dmcontrol_t;

  typedef struct packed {
    logic [31:24] zero1;
    logic [23:20] nscratch;
    logic [19:17] zero0;
    logic         dataaccess;
    logic [15:12] datasize;
    logic [11:0]  dataaddr;
  } hartinfo_t;

  typedef enum logic [2:0] {
    CmdErrNone, CmdErrBusy, CmdErrNotSupported,
    CmdErrorException, CmdErrorHaltResume,
    CmdErrorBus, CmdErrorOther = 7
  } cmderr_e;

  typedef struct packed {
    logic [31:29] zero3;
    logic [28:24] progbufsize;
    logic [23:13] zero2;
    logic         busy;
    logic         zero1;
    cmderr_e      cmderr;
    logic [7:4]   zero0;
    logic [3:0]   datacount;
  } abstractcs_t;

  typedef enum logic [7:0] {
    AccessRegister = 8'h0,
    QuickAccess    = 8'h1,
    AccessMemory   = 8'h2
  } cmd_e;

  typedef struct packed {
    cmd_e        cmdtype;
    logic [23:0] control;
  } command_t;

  typedef struct packed {
    logic [31:16] autoexecprogbuf;
    logic [15:12] zero0;
    logic [11:0]  autoexecdata;
  } abstractauto_t;

  typedef struct packed {
    logic         zero1;
    logic [22:20] aarsize;
    logic         aarpostincrement;
    logic         postexec;
    logic         transfer;
    logic         write;
    logic [15:0]  regno;
  } ac_ar_cmd_t;

  // DTM
  typedef enum logic [1:0] {
    DTM_NOP   = 2'h0,
    DTM_READ  = 2'h1,
    DTM_WRITE = 2'h2
  } dtm_op_e;

  typedef struct packed {
    logic [31:29] sbversion;
    logic [28:23] zero0;
    logic         sbbusyerror;
    logic         sbbusy;
    logic         sbreadonaddr;
    logic [19:17] sbaccess;
    logic         sbautoincrement;
    logic         sbreadondata;
    logic [14:12] sberror;
    logic [11:5]  sbasize;
    logic         sbaccess128;
    logic         sbaccess64;
    logic         sbaccess32;
    logic         sbaccess16;
    logic         sbaccess8;
  } sbcs_t;

  localparam logic[1:0] DTM_SUCCESS = 2'h0;

  typedef struct packed {
    logic [6:0]  addr;
    dtm_op_e     op;
    logic [31:0] data;
  } dmi_req_t;

  typedef struct packed  {
    logic [31:0] data;
    logic [1:0]  resp;
  } dmi_resp_t;

  // privilege levels
  typedef enum logic[1:0] {
    PRIV_LVL_M = 2'b11,
    PRIV_LVL_S = 2'b01,
    PRIV_LVL_U = 2'b00
  } priv_lvl_t;

  // debugregs in core
  typedef struct packed {
    logic [31:28]     xdebugver;
    logic [27:16]     zero2;
    logic             ebreakm;
    logic             zero1;
    logic             ebreaks;
    logic             ebreaku;
    logic             stepie;
    logic             stopcount;
    logic             stoptime;
    logic [8:6]       cause;
    logic             zero0;
    logic             mprven;
    logic             nmip;
    logic             step;
    priv_lvl_t        prv;
  } dcsr_t;

  // CSRs
  typedef enum logic [11:0] {
    // Floating-Point CSRs
    CSR_FFLAGS         = 12'h001,
    CSR_FRM            = 12'h002,
    CSR_FCSR           = 12'h003,
    CSR_FTRAN          = 12'h800,
    // Supervisor Mode CSRs
    CSR_SSTATUS        = 12'h100,
    CSR_SIE            = 12'h104,
    CSR_STVEC          = 12'h105,
    CSR_SCOUNTEREN     = 12'h106,
    CSR_SSCRATCH       = 12'h140,
    CSR_SEPC           = 12'h141,
    CSR_SCAUSE         = 12'h142,
    CSR_STVAL          = 12'h143,
    CSR_SIP            = 12'h144,
    CSR_SATP           = 12'h180,
    // Machine Mode CSRs
    CSR_MSTATUS        = 12'h300,
    CSR_MISA           = 12'h301,
    CSR_MEDELEG        = 12'h302,
    CSR_MIDELEG        = 12'h303,
    CSR_MIE            = 12'h304,
    CSR_MTVEC          = 12'h305,
    CSR_MCOUNTEREN     = 12'h306,
    CSR_MSCRATCH       = 12'h340,
    CSR_MEPC           = 12'h341,
    CSR_MCAUSE         = 12'h342,
    CSR_MTVAL          = 12'h343,
    CSR_MIP            = 12'h344,
    CSR_PMPCFG0        = 12'h3A0,
    CSR_PMPADDR0       = 12'h3B0,
    CSR_MVENDORID      = 12'hF11,
    CSR_MARCHID        = 12'hF12,
    CSR_MIMPID         = 12'hF13,
    CSR_MHARTID        = 12'hF14,
    CSR_MCYCLE         = 12'hB00,
    CSR_MINSTRET       = 12'hB02,
    CSR_DCACHE         = 12'h701,
    CSR_ICACHE         = 12'h700,

    CSR_TSELECT        = 12'h7A0,
    CSR_TDATA1         = 12'h7A1,
    CSR_TDATA2         = 12'h7A2,
    CSR_TDATA3         = 12'h7A3,
    CSR_TINFO          = 12'h7A4,

    // Debug CSR
    CSR_DCSR           = 12'h7b0,
    CSR_DPC            = 12'h7b1,
    CSR_DSCRATCH0      = 12'h7b2, // optional
    CSR_DSCRATCH1      = 12'h7b3, // optional

    // Counters and Timers
    CSR_CYCLE          = 12'hC00,
    CSR_TIME           = 12'hC01,
    CSR_INSTRET        = 12'hC02
  } csr_reg_t;


  // Instruction Generation Helpers
  function automatic logic [31:0] jal (logic [4:0]  rd,
                                       logic [20:0] imm);
    // OpCode Jal
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
  endfunction

  function automatic logic [31:0] jalr (logic [4:0]  rd,
                                        logic [4:0]  rs1,
                                        logic [11:0] offset);
    // OpCode Jal
    return {offset[11:0], rs1, 3'b0, rd, 7'h67};
  endfunction

  function automatic logic [31:0] andi (logic [4:0]  rd,
                                        logic [4:0]  rs1,
                                        logic [11:0] imm);
    // OpCode andi
    return {imm[11:0], rs1, 3'h7, rd, 7'h13};
  endfunction

  function automatic logic [31:0] slli (logic [4:0] rd,
                                        logic [4:0] rs1,
                                        logic [5:0] shamt);
    // OpCode slli
    return {6'b0, shamt[5:0], rs1, 3'h1, rd, 7'h13};
  endfunction

  function automatic logic [31:0] srli (logic [4:0] rd,
                                        logic [4:0] rs1,
                                        logic [5:0] shamt);
    // OpCode srli
    return {6'b0, shamt[5:0], rs1, 3'h5, rd, 7'h13};
  endfunction

  function automatic logic [31:0] load (logic [2:0]  size,
                                        logic [4:0]  dest,
                                        logic [4:0]  base,
                                        logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'h03};
  endfunction

  function automatic logic [31:0] auipc (logic [4:0]  rd,
                                         logic [20:0] imm);
    // OpCode Auipc
    return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h17};
  endfunction

  function automatic logic [31:0] store (logic [2:0]  size,
                                         logic [4:0]  src,
                                         logic [4:0]  base,
                                         logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'h23};
  endfunction

  function automatic logic [31:0] float_load (logic [2:0]  size,
                                              logic [4:0]  dest,
                                              logic [4:0]  base,
                                              logic [11:0] offset);
    // OpCode Load
    return {offset[11:0], base, size, dest, 7'b00_001_11};
  endfunction

  function automatic logic [31:0] float_store (logic [2:0]  size,
                                               logic [4:0]  src,
                                               logic [4:0]  base,
                                               logic [11:0] offset);
    // OpCode Store
    return {offset[11:5], src, base, size, offset[4:0], 7'b01_001_11};
  endfunction

  function automatic logic [31:0] csrw (csr_reg_t   csr,
                                        logic [4:0] rs1);
    // CSRRW, rd, OpCode System
    return {csr, rs1, 3'h1, 5'h0, 7'h73};
  endfunction

  function automatic logic [31:0] csrr (csr_reg_t   csr,
                                        logic [4:0] dest);
    // rs1, CSRRS, rd, OpCode System
    return {csr, 5'h0, 3'h2, dest, 7'h73};
  endfunction

  function automatic logic [31:0] branch(logic [4:0]  src2,
                                         logic [4:0]  src1,
                                         logic [2:0]  funct3,
                                         logic [11:0] offset);
    // OpCode Branch
    return {offset[11], offset[9:4], src2, src1, funct3,
        offset[3:0], offset[10], 7'b11_000_11};
  endfunction

  function automatic logic [31:0] ebreak ();
    return 32'h00100073;
  endfunction

  function automatic logic [31:0] wfi ();
    return 32'h10500073;
  endfunction

  function automatic logic [31:0] nop ();
    return 32'h00000013;
  endfunction

  function automatic logic [31:0] illegal ();
    return 32'h00000000;
  endfunction

endpackage : dm
