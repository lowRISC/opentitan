// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_item extends uvm_sequence_item;

  entropy_src_xht_req_t req;
  entropy_src_xht_rsp_t rsp;

  `uvm_object_utils(entropy_src_xht_item)
  `uvm_object_new

endclass
