// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_otf_mem_entry extends uvm_object;
  `uvm_object_utils(flash_otf_mem_entry)
  `uvm_object_new

  logic [BankAddrW-1:0] mem_addr;
  logic [flash_phy_pkg::FullDataWidth-1:0] mem_wdata;
  flash_part_e mem_part;
  logic [InfoTypesWidth-1:0] mem_info_sel;


endclass // flash_otf_mem_entry
