// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash phy macro package
// This has the interface to the flash macro wrapper. It is top-specific,
// but all dependencies are via macro wrapper overridden parameters, so
// it is okay for the flash macro wrapper to depend on this package.

package flash_phy_macro_pkg;

  import flash_ctrl_pkg::ProgTypes;

  parameter int unsigned NumBanks = flash_ctrl_top_specific_pkg::NumBanks;
  parameter int unsigned InfosPerBank = flash_ctrl_top_specific_pkg::InfosPerBank;
  parameter int unsigned InfoTypes = flash_ctrl_top_specific_pkg::InfoTypes;
  parameter int unsigned InfoTypesWidth = flash_ctrl_top_specific_pkg::InfoTypesWidth;
  parameter int unsigned PagesPerBank = flash_ctrl_top_specific_pkg::PagesPerBank;
  parameter int unsigned WordsPerPage = flash_ctrl_top_specific_pkg::WordsPerPage;
  parameter int unsigned DataWidth = flash_ctrl_top_specific_pkg::DataWidth +
                                     flash_ctrl_top_specific_pkg::MetaDataWidth;
  parameter int unsigned BankAddrW = flash_ctrl_top_specific_pkg::BankAddrW;
  parameter int TestModeWidth = 2;

  // Transaction request to flash macro
  typedef struct packed {
    logic rd_req;
    logic prog_req;
    logic prog_last;
    flash_ctrl_pkg::flash_prog_e prog_type;
    logic pg_erase_req;
    logic bk_erase_req;
    logic erase_suspend_req;
    logic he;
    logic [BankAddrW-1:0] addr;
    flash_ctrl_pkg::flash_part_e part;
    logic [InfoTypesWidth-1:0] info_sel;
    logic [DataWidth-1:0] prog_full_data;
  } flash_phy_macro_bank_req_t;

  typedef struct packed {
    flash_phy_macro_bank_req_t [NumBanks-1:0] bank_reqs;
  } flash_phy_macro_req_t;

  // Transaction response from flash macro
  typedef struct packed {
    logic ack;
    logic done;
    logic [DataWidth-1:0] rdata;
  } flash_phy_macro_bank_rsp_t;

  typedef struct packed {
    flash_phy_macro_bank_rsp_t [NumBanks-1:0] bank_rsps;
  } flash_phy_macro_rsp_t;

  // Status of flash macro
  typedef struct packed {
    // What program types flash macro supports
    logic [ProgTypes-1:0] prog_type_avail;
    // Asserted while flash is getting initialized
    logic                 init_busy;
    // Macro error
    logic                 flash_err;
    // Alert indications for the phy to connect to alert sender
    logic                 fatal_alert;
    logic                 recov_alert;
  } flash_macro_status_t;

endpackage : flash_phy_macro_pkg
