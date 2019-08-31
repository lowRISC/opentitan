// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class xbar_seq_item;
  rand logic [31:0]        addr;
  rand logic [31:0]        data;
  rand logic [3:0]         wstrb;
  rand xbar_pkg::xbar_op_e op;

  function xbar_seq_item copy();
    copy = new;
    copy.addr = this.addr;
    copy.data = this.data;
    copy.wstrb = this.wstrb;
    copy.op = this.op;
    return copy;
  endfunction : copy
endclass : xbar_seq_item
