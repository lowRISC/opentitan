// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package csrng_pkg;

  //-------------------------
  // Application Interfaces
  //-------------------------

  parameter int unsigned GENBITS_BUS_WIDTH = 128;
  parameter int unsigned CSRNG_CMD_WIDTH = 32;
  parameter int unsigned FIPS_GENBITS_BUS_WIDTH = entropy_src_pkg::FIPS_BUS_WIDTH +
                         GENBITS_BUS_WIDTH;
  parameter int unsigned MainSmStateWidth = 8;

  // instantiation interface
  typedef struct packed {
    logic                       csrng_req_valid;
    logic [CSRNG_CMD_WIDTH-1:0] csrng_req_bus;
    logic                       genbits_ready;
  } csrng_req_t;

  typedef struct packed {
    logic                         csrng_req_ready;
    logic                         csrng_rsp_ack;
    logic                         csrng_rsp_sts;
    logic                         genbits_valid;
    logic                         genbits_fips;
    logic [GENBITS_BUS_WIDTH-1:0] genbits_bus;
  } csrng_rsp_t;

  parameter csrng_req_t CSRNG_REQ_DEFAULT = '{default: '0};
  parameter csrng_rsp_t CSRNG_RSP_DEFAULT = '{default: '0};

  typedef enum logic [2:0] {
    INV  = 3'h0,
    INS  = 3'h1,
    RES  = 3'h2,
    GEN  = 3'h3,
    UPD  = 3'h4,
    UNI  = 3'h5,
    GENB = 3'h6,
    GENU = 3'h7
  } acmd_e;


  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 15 -n 8 \
  //      -s 1300573258 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||| (32.38%)
  //  4: |||||||||||||||||||| (35.24%)
  //  5: |||||||| (15.24%)
  //  6: |||||| (11.43%)
  //  7: ||| (5.71%)
  //  8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 7
  //
  typedef    enum logic [MainSmStateWidth-1:0] {
    MainSmIdle          = 8'b01001110, // idle
    MainSmParseCmd      = 8'b10111011, // parse the cmd
    MainSmInstantPrep   = 8'b11000001, // instantiate prep
    MainSmInstantReq    = 8'b01010100, // instantiate request (takes adata or entropy)
    MainSmReseedPrep    = 8'b11011101, // reseed prep
    MainSmReseedReq     = 8'b01011011, // reseed request (takes adata and entropy and Key,V,RC)
    MainSmGeneratePrep  = 8'b11101111, // generate request (takes adata? and Key,V,RC)
    MainSmGenerateReq   = 8'b00100100, // generate request (takes adata? and Key,V,RC)
    MainSmUpdatePrep    = 8'b00110001, // update prep
    MainSmUpdateReq     = 8'b10010000, // update request (takes adata and Key,V,RC)
    MainSmUninstantPrep = 8'b11110110, // uninstantiate prep
    MainSmUninstantReq  = 8'b01100011, // uninstantiate request
    MainSmClrAData      = 8'b00000010, // clear out the additional data packer fifo
    MainSmCmdCompWait   = 8'b10111100, // wait for command to complete
    MainSmError         = 8'b01111000  // error state, results in fatal alert
  } main_sm_state_e;

  parameter int CsKeymgrDivWidth = 384;
  typedef logic [CsKeymgrDivWidth-1:0] cs_keymgr_div_t;

endpackage : csrng_pkg
