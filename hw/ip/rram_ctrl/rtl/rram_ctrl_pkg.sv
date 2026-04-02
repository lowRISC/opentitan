// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Controller Package
//

package rram_ctrl_pkg;

  // RRAM parameters
  parameter int unsigned TotalBytes      = 2*1024*1024; // 2 MiB
  parameter int unsigned TotalInfoBytes  = 4*1024; // 4 KiB
  parameter int unsigned TotalOtpBytes   = 2*1024 + 512; // (2 KiB + 0.5KiB interity)
  parameter int unsigned DataWidth       = 128; // 1 RRAM word in bits
  parameter int unsigned WordsPerPage    = 32; // Number of RRAM words per page
  parameter int unsigned TotalPages      = TotalBytes / (DataWidth / 8) / WordsPerPage; // 4096
  parameter int unsigned TotalInfoPages  = TotalInfoBytes / (DataWidth / 8) / WordsPerPage; // 8
  parameter int unsigned MaxWrWords      = 32; // max. number of words that can be written at once
  parameter int unsigned OtpPages        = TotalOtpBytes / (DataWidth / 8) / WordsPerPage; // 5
  parameter int unsigned DataPages       = TotalPages - OtpPages; // 4091
  parameter int unsigned OtpStartPage    = DataPages;

  parameter int unsigned BusWidth        = top_pkg::TL_DW;
  parameter int unsigned BusIntgWidth    = tlul_pkg::DataIntgWidth;
  parameter int unsigned BusFullWidth    = BusWidth + BusIntgWidth;

  parameter int unsigned MpRegions       = 8;  // controller protection regions
  parameter int unsigned TotalMpRegions  = MpRegions + 2; // + default region and init region

  // RRAM phy parameters
  parameter int unsigned DataByteWidth   = prim_util_pkg::vbits(DataWidth / 8);
  parameter int unsigned PageW           = prim_util_pkg::vbits(TotalPages);
  parameter int unsigned InfoPageW       = prim_util_pkg::vbits(TotalInfoPages);
  parameter int unsigned WordW           = prim_util_pkg::vbits(WordsPerPage);
  parameter int unsigned AddrW           = PageW + WordW; // full RRAM range

  // RRAM ctrl / bus parameters
  parameter int unsigned BusBytes        = BusWidth / 8;
  parameter int unsigned BusByteWidth    = prim_util_pkg::vbits(BusBytes);
  parameter int unsigned WidthMultiple   = DataWidth / BusWidth;
  parameter int unsigned WordSelW        = prim_util_pkg::vbits(WidthMultiple);
  // Maximum number of bus words that can be written at once
  parameter int unsigned BusWordsPerPage = WordsPerPage * WidthMultiple;
  parameter int unsigned BusWordW        = prim_util_pkg::vbits(BusWordsPerPage);
  parameter int unsigned BusAddrW        = PageW + BusWordW;
  parameter int unsigned BusAddrByteW    = BusAddrW + BusByteWidth;

  //////////////////////////////////
  // RRAM operation related enums //
  //////////////////////////////////

  // RRAM partition type
  typedef enum logic {
    RramPartData = 1'b0,
    RramPartInfo = 1'b1
  } rram_part_e;

  //////////////////////////////////////////////////////////
  // Open-Source interface RRAM macro <-> RRAM controller //
  //////////////////////////////////////////////////////////
  typedef struct packed {
    logic                 rd_req;
    logic                 wr_req;
    logic                 wr_last;
    logic [AddrW-1:0]     addr;
    logic [DataWidth-1:0] wr_data;
    rram_part_e           part;
    logic                 ecc_en;
  } rram_macro_req_t;

  typedef struct packed {
    logic                 ack;
    logic                 done;
    logic                 err;
    logic                 ecc_err;
    logic [DataWidth-1:0] rd_data;
    logic                 init_done;
    logic                 fatal_err;
    logic                 recov_err;
  } rram_macro_rsp_t;

endpackage : rram_ctrl_pkg
