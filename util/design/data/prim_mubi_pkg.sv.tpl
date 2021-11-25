// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    util/design/gen-mubi.py
//
// This package defines common multibit signal types, active high and active low values and
// the corresponding functions to test whether the values are set or not.

package prim_mubi_pkg;

<%
from mubi import prim_mubi
%>\
% for n in range(1, n_max_nibbles + 1):
<%
   nbits = n * 4
   hdr = f'// {nbits} Bit Multibit Type and Functions //'
   box_slashes = '/' * len(hdr)

   MuBiWidth = f'MuBi{nbits}Width'
   MuBiTrue = f'MuBi{nbits}True'
   MuBiFalse = f'MuBi{nbits}False'

   true_hex = f"{nbits}'h" + prim_mubi.mubi_value_as_hexstr(True, nbits)
   false_hex = f"{nbits}'h" + prim_mubi.mubi_value_as_hexstr(False, nbits)

   mubi_type = f'mubi{nbits}_t'
   fun_pfx = f'mubi{nbits}_'

%>\
  ${box_slashes}
  ${hdr}
  ${box_slashes}

  parameter int ${MuBiWidth} = ${nbits};
  typedef enum logic [${MuBiWidth}-1:0] {
    ${MuBiTrue} = ${true_hex}, // enabled
    ${MuBiFalse} = ${false_hex}  // disabled
  } ${mubi_type};

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic ${fun_pfx}test_invalid(${mubi_type} val);
    return ~(val inside {${MuBiTrue}, ${MuBiFalse}});
  endfunction : ${fun_pfx}test_invalid

  // Convert a 1 input value to a mubi output
  function automatic ${mubi_type} ${fun_pfx}bool_to_mubi(logic val);
    return val ? ${MuBiTrue} : ${MuBiFalse};
  endfunction : ${fun_pfx}bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic ${fun_pfx}test_true_strict(${mubi_type} val);
    return ${MuBiTrue} == val;
  endfunction : ${fun_pfx}test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic ${fun_pfx}test_false_strict(${mubi_type} val);
    return ${MuBiFalse} == val;
  endfunction : ${fun_pfx}test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic ${fun_pfx}test_true_loose(${mubi_type} val);
    return ${MuBiFalse} != val;
  endfunction : ${fun_pfx}test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic ${fun_pfx}test_false_loose(${mubi_type} val);
    return ${MuBiTrue} != val;
  endfunction : ${fun_pfx}test_false_loose


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
  function automatic ${mubi_type} ${fun_pfx}or(${mubi_type} a, ${mubi_type} b, ${mubi_type} act);
    logic [${MuBiWidth}-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < ${MuBiWidth}; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return ${mubi_type}'(out);
  endfunction : ${fun_pfx}or

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
  function automatic ${mubi_type} ${fun_pfx}and(${mubi_type} a, ${mubi_type} b, ${mubi_type} act);
    logic [${MuBiWidth}-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < ${MuBiWidth}; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return ${mubi_type}'(out);
  endfunction : ${fun_pfx}and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic ${mubi_type} ${fun_pfx}or_hi(${mubi_type} a, ${mubi_type} b);
    return ${fun_pfx}or(a, b, ${MuBiTrue});
  endfunction : ${fun_pfx}or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic ${mubi_type} ${fun_pfx}and_hi(${mubi_type} a, ${mubi_type} b);
    return ${fun_pfx}and(a, b, ${MuBiTrue});
  endfunction : ${fun_pfx}and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic ${mubi_type} ${fun_pfx}or_lo(${mubi_type} a, ${mubi_type} b);
    return ${fun_pfx}or(a, b, ${MuBiFalse});
  endfunction : ${fun_pfx}or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic ${mubi_type} ${fun_pfx}and_lo(${mubi_type} a, ${mubi_type} b);
    return ${fun_pfx}and(a, b, ${MuBiFalse});
  endfunction : ${fun_pfx}and_lo

% endfor
endpackage : prim_mubi_pkg
