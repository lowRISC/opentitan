// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package csrng_pkg;

  parameter int unsigned NumAppsLg = $clog2(csrng_reg_pkg::NumApps);

  // Main design parameters
  // We use the suffix 'Len' (as opposed to 'Width') to stick to the symbols used in the
  // NIST SP 800-90A algorithm specification.

  // Size of the generated random number blocks in bits and the internal state variable 'v'
  parameter int unsigned BlkLen = 128;
  // Cipher key size in bits
  parameter int unsigned KeyLen = 256;
  // Seed size in bits; must be equal to the sum of BlkLen and KeyLen
  parameter int unsigned SeedLen = BlkLen + KeyLen;
  // Width of the counter field used as input to the cipher
  // Caution: Not to be confused with the reseed counter width! These two are independent
  parameter int unsigned CtrLen = 32;
  parameter int unsigned RsCtrWidth = 32;

  // Width of the counter in the command stages to count the amount of generated random bits
  parameter int unsigned GenBitsCtrWidth = 12;

  // Commonly used internal signal widths
  parameter int unsigned CmdWidth = 3;
  parameter int unsigned InstIdWidth = 4;

  // Width of the application command bus (matches the 32b TLUL bus width)
  parameter int unsigned CmdBusWidth = 32;

  // Maximum number of 32b words additionally supplied on the application interfaces
  parameter int unsigned CmdMaxClen = 12;
  parameter int unsigned CmdFifoDepth = 2;
  parameter int unsigned CmdFifoDepthLg = $clog2(CmdFifoDepth);

  parameter int unsigned GENBITS_BUS_WIDTH = BlkLen;
  parameter int unsigned FIPS_GENBITS_BUS_WIDTH = entropy_src_pkg::FIPS_BUS_WIDTH +
                         GENBITS_BUS_WIDTH;

  //-------------------------
  // Application Interface
  //-------------------------

  typedef struct packed {
    logic                   csrng_req_valid;
    logic [CmdBusWidth-1:0] csrng_req_bus;
    logic                   genbits_ready;
  } csrng_req_t;

  parameter int unsigned CmdStatusWidth = 3;

  typedef enum logic [CmdStatusWidth-1:0] {
    CMD_STS_SUCCESS              = 'h0,
    CMD_STS_INVALID_ACMD         = 'h1,
    CMD_STS_INVALID_GEN_CMD      = 'h2,
    CMD_STS_INVALID_CMD_SEQ      = 'h3,
    CMD_STS_RESEED_CNT_EXCEEDED  = 'h4,
    CMD_STS_UNDRIVEN             = 'z
  } csrng_cmd_sts_e;

  typedef struct packed {
    logic                         csrng_req_ready;
    logic                         csrng_rsp_ack;
    csrng_cmd_sts_e               csrng_rsp_sts;
    logic                         genbits_valid;
    logic                         genbits_fips;
    logic [GENBITS_BUS_WIDTH-1:0] genbits_bus;
  } csrng_rsp_t;

  parameter csrng_req_t CSRNG_REQ_DEFAULT = '{default: '0};
  parameter csrng_rsp_t CSRNG_RSP_DEFAULT = '0;

  typedef enum logic [CmdWidth-1:0] {
    INV  = 3'h0,
    INS  = 3'h1,
    RES  = 3'h2,
    GEN  = 3'h3,
    UPD  = 3'h4,
    UNI  = 3'h5
  } acmd_e;

  typedef struct packed {
    logic  [7:0] resv;
    logic [11:0] glen;
    logic  [3:0] flag0;
    logic  [3:0] clen;
    logic        gap; // acmd is defined as 4 bits wide but only 3 are used
    acmd_e       acmd;
  } csrng_cmd_t;

  //------------------------------------------
  // Struct data types for the core data path
  //------------------------------------------

  typedef struct packed {
    logic                   fips;
    logic  [RsCtrWidth-1:0] rs_ctr;
    logic     [SeedLen-1:0] pdata;
    logic   [NumAppsLg-1:0] inst_id;
    acmd_e                  cmd;
    logic      [KeyLen-1:0] key;
    logic      [BlkLen-1:0] v;
  } csrng_core_data_t;

  typedef struct packed {
    logic [KeyLen-1:0] key;
    logic [BlkLen-1:0] v;
  } csrng_key_v_t;

  // Do not reorder these fields - software expects them in this order when doing the raw
  // state readout through the register interface.
  typedef struct packed {
    logic                  fips;
    logic                  inst_state;
    logic     [KeyLen-1:0] key;
    logic     [BlkLen-1:0] v;
    logic [RsCtrWidth-1:0] rs_ctr;
  } csrng_state_t;

  parameter int unsigned StateWidth    = $bits(csrng_state_t);

  parameter int unsigned MainSmStateWidth = 6;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 8 -n 6 \
  //     -s 137328258 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  typedef enum logic [MainSmStateWidth-1:0] {
    MainSmIdle        = 6'b110111, // idle
    MainSmParseCmd    = 6'b011101, // parse the cmd
    MainSmEntropyReq  = 6'b001110, // request entropy if necessary
    MainSmCmdPrep     = 6'b000011, // delay cycle for command request (?)
    MainSmCmdVld      = 6'b010000, // command request to core data path
    MainSmClrAData    = 6'b111010, // clear out the additional data packer fifo
    MainSmCmdCompWait = 6'b100100, // wait for command to complete
    MainSmError       = 6'b101001  // error state, results in fatal alert
  } main_sm_state_e;

  parameter int CsKeymgrDivWidth = 384;
  typedef logic [CsKeymgrDivWidth-1:0] cs_keymgr_div_t;

endpackage : csrng_pkg
