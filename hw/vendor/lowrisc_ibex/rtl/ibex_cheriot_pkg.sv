// Copyright lowRISC contributors.
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_cheriot_pkg;

  parameter int unsigned TOP_W     = 9;
  parameter int unsigned BOT_W     = 9;
  parameter int unsigned EXP_W     = 5;
  parameter int unsigned OTYPE_W   = 3;
  parameter int unsigned CPERMS_W  = 6;


  // Expand the compressed 4-bit exponent field stored in a capability to its
  // 5-bit internal representation.(page 70, CHERIoT Architecture specification, Version 1.0).
  function automatic logic [EXP_W-1:0] get_exponent(logic [3:0] exponent_stored);
    return (exponent_stored != 4'hf) ? {1'b0, exponent_stored} : 5'd24;
  endfunction


  // Check if a capability's permissions correspond to a sealing capability.
  // Only the low 5 bits of the (6-bit) compressed permissions field are decoded here.
  function automatic logic is_sealing_cap(logic [4:0] cperms);
    return (cperms[4:3] == 2'b00) && (|cperms[2:0]);
  endfunction


  // Obtain 33-bit representation of top or bottom depending on the inputs.
  function automatic logic[32:0] get_bound33(logic [TOP_W-1:0] top, logic [1:0]  cor,
                                             logic [EXP_W-1:0] exponent, logic [31:0] addr);
    logic [32:0] t1, t2, mask, cor_val;

    if (cor[1])
      // negative sign extension
      cor_val = {33{cor[1]}};
    else
      cor_val = {32'h0, (~cor[1]) & cor[0]};

    cor_val = (cor_val << exponent) << TOP_W;
    mask    = (33'h1_ffff_ffff << exponent) << TOP_W;

    // apply correction and truncate
    t1 = ({1'b0, addr} & mask) + cor_val;
    // extend to 32 bit
    t2 = {24'h0, top};
    t1 = t1 | (t2 << exponent);

    return t1;
  endfunction


  // Update the top/base correction for a cap
  function automatic logic [2:0] update_temp_fields(logic [TOP_W-1:0] top, logic [BOT_W-1:0] base,
                                                    logic [BOT_W-1:0] addrmi);
    logic top_hi, addr_hi;
    logic [2:0] res3;

    top_hi   = (top < base);
    addr_hi  = (addrmi < base);

    // top_cor
    res3[2:1] = (top_hi == addr_hi)? 2'b00 : ((top_hi && (!addr_hi))? 2'b01 : 2'b11);

    // base_cor
    res3[0] = (addr_hi) ? 1'b1 : 1'b0;

    return res3;
  endfunction

endpackage
