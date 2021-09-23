// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    hw/ip/prim/util/generate_prim_mubi_pkg.py hw/ip/prim/data/prim_mubi_pkg.sv.tpl >
//                                              hw/ip/prim/rtl/prim_mubi_pkg.sv
//
// This package defines common multibit signal types, active high and active low values and
// the corresponding functions to test whether the values are set or not.

package prim_mubi_pkg;

% for n in range(1, n_max_nibbles + 1):
<%
  nbits = n * 4
  hi_val = ''
  lo_val = ''
  for k in range(1,n+1):
    hi_val = ('5' if (k % 2) else 'A') + hi_val
    lo_val = ('A' if (k % 2) else '5') + lo_val
%>\
  //////////////////////////////////////////////
  // ${nbits} Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi${nbits}Width = ${nbits};
  typedef enum logic [MuBi${nbits}Width-1:0] {
    MuBi${nbits}Hi = ${nbits}'h${hi_val}, // enabled
    MuBi${nbits}Lo = ${nbits}'h${lo_val}  // disabled
  } mubi${nbits}_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi${nbits}_e mubi${nbits}_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi${nbits}_e mubi${nbits}_hi_value();
    return MuBi${nbits}Hi;
  endfunction : mubi${nbits}_hi_value

  // Return the multibit value to signal "disabled".
  function automatic mubi${nbits}_e mubi${nbits}_lo_value();
    return MuBi${nbits}Lo;
  endfunction : mubi${nbits}_lo_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Hi.
  function automatic logic mubi${nbits}_tst_hi_strict(mubi${nbits}_e val);
    return MuBi${nbits}Hi == val;
  endfunction : mubi${nbits}_tst_hi_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Lo.
  function automatic logic mubi${nbits}_tst_lo_strict(mubi${nbits}_e val);
    return MuBi${nbits}Lo == val;
  endfunction : mubi${nbits}_tst_lo_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than Lo as "enabled".
  function automatic logic mubi${nbits}_tst_hi_loose(mubi${nbits}_e val);
    return MuBi${nbits}Lo != val;
  endfunction : mubi${nbits}_tst_hi_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than Hi as "disabled".
  function automatic logic mubi${nbits}_tst_lo_loose(mubi${nbits}_e val);
    return MuBi${nbits}Hi != val;
  endfunction : mubi${nbits}_tst_lo_loose


  // Performs a logical OR operation between two multibit values.
  // This treats "act" as logical 1, and all other values are
  // treated as 0. Truth table:
  //
  // A    | B    | OUT
  //------+------+-----
  // !act | !act | !act
  // act  | !act | act
  // !act | act  | act
  // act  | act  | act
  //
  function automatic mubi${nbits}_e mubi${nbits}_or(mubi${nbits}_e a, mubi${nbits}_e b, mubi${nbits}_e act);
    logic [MuBi${nbits}Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi${nbits}Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi${nbits}_e'(out);
  endfunction : mubi${nbits}_or

  // Performs a logical AND operation between two multibit values.
  // This treats "act" as logical 1, and all other values are
  // treated as 0. Truth table:
  //
  // A    | B    | OUT
  //------+------+-----
  // !act | !act | !act
  // act  | !act | !act
  // !act | act  | !act
  // act  | act  | act
  //
  function automatic mubi${nbits}_e mubi${nbits}_and(mubi${nbits}_e a, mubi${nbits}_e b, mubi${nbits}_e act);
    logic [MuBi${nbits}Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi${nbits}Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi${nbits}_e'(out);
  endfunction : mubi${nbits}_and

  // Performs a logical OR operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_or_hi(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_or(a, b, MuBi${nbits}Hi);
  endfunction : mubi${nbits}_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_and_hi(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_and(a, b, MuBi${nbits}Hi);
  endfunction : mubi${nbits}_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_or_lo(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_or(a, b, MuBi${nbits}Lo);
  endfunction : mubi${nbits}_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_and_lo(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_and(a, b, MuBi${nbits}Lo);
  endfunction : mubi${nbits}_and_lo

% endfor
endpackage : prim_mubi_pkg
