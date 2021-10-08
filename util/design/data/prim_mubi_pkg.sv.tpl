// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    hw/ip/prim/util/generate_prim_mubi.py
//
// This package defines common multibit signal types, active high and active low values and
// the corresponding functions to test whether the values are set or not.

package prim_mubi_pkg;

<%
import prim_mubi as prim_mubi
%>\
% for n in range(1, N_MAX_NIBBLES + 1):
<%
   nbits = n * 4
%>\
  //////////////////////////////////////////////
  // ${nbits} Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi${nbits}Width = ${nbits};
  typedef enum logic [MuBi${nbits}Width-1:0] {
    MuBi${nbits}True = ${nbits}'h${prim_mubi.mubi_value(True, nbits)}, // enabled
    MuBi${nbits}False = ${nbits}'h${prim_mubi.mubi_value(False, nbits)}  // disabled
  } mubi${nbits}_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi${nbits}_e mubi${nbits}_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi${nbits}_e mubi${nbits}_true_value();
    return MuBi${nbits}True;
  endfunction : mubi${nbits}_true_value

  // Return the multibit value to signal "disabled".
  function automatic mubi${nbits}_e mubi${nbits}_false_value();
    return MuBi${nbits}False;
  endfunction : mubi${nbits}_false_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi${nbits}_test_true_strict(mubi${nbits}_e val);
    return MuBi${nbits}True == val;
  endfunction : mubi${nbits}_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi${nbits}_test_false_strict(mubi${nbits}_e val);
    return MuBi${nbits}False == val;
  endfunction : mubi${nbits}_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi${nbits}_test_true_loose(mubi${nbits}_e val);
    return MuBi${nbits}False != val;
  endfunction : mubi${nbits}_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi${nbits}_test_false_loose(mubi${nbits}_e val);
    return MuBi${nbits}True != val;
  endfunction : mubi${nbits}_test_false_loose


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
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_or_hi(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_or(a, b, MuBi${nbits}True);
  endfunction : mubi${nbits}_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_and_hi(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_and(a, b, MuBi${nbits}True);
  endfunction : mubi${nbits}_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_or_lo(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_or(a, b, MuBi${nbits}False);
  endfunction : mubi${nbits}_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi${nbits}_e mubi${nbits}_and_lo(mubi${nbits}_e a, mubi${nbits}_e b);
    return mubi${nbits}_and(a, b, MuBi${nbits}False);
  endfunction : mubi${nbits}_and_lo

% endfor
endpackage : prim_mubi_pkg
