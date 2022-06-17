// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_phy_prim_item extends uvm_sequence_item;

  `uvm_object_utils_begin(flash_phy_prim_item)
  `uvm_object_utils_end

  flash_phy_pkg::flash_phy_prim_flash_req_t req;
  flash_phy_pkg::flash_phy_prim_flash_rsp_t rsp;

  fdata_q_t fq;
  `uvm_object_new

endclass
