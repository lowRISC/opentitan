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

  //////////////////////////////////////////////
  // 4 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi4Width = 4;
  typedef enum logic [MuBi4Width-1:0] {
    MuBi4True = 4'hA, // enabled
    MuBi4False = 4'h5  // disabled
  } mubi4_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi4_e mubi4_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi4_e mubi4_true_value();
    return MuBi4True;
  endfunction : mubi4_true_value

  // Return the multibit value to signal "disabled".
  function automatic mubi4_e mubi4_false_value();
    return MuBi4False;
  endfunction : mubi4_false_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi4_test_true_strict(mubi4_e val);
    return MuBi4True == val;
  endfunction : mubi4_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi4_test_false_strict(mubi4_e val);
    return MuBi4False == val;
  endfunction : mubi4_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi4_test_true_loose(mubi4_e val);
    return MuBi4False != val;
  endfunction : mubi4_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi4_test_false_loose(mubi4_e val);
    return MuBi4True != val;
  endfunction : mubi4_test_false_loose


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
  function automatic mubi4_e mubi4_or(mubi4_e a, mubi4_e b, mubi4_e act);
    logic [MuBi4Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi4Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi4_e'(out);
  endfunction : mubi4_or

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
  function automatic mubi4_e mubi4_and(mubi4_e a, mubi4_e b, mubi4_e act);
    logic [MuBi4Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi4Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi4_e'(out);
  endfunction : mubi4_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_or_hi(mubi4_e a, mubi4_e b);
    return mubi4_or(a, b, MuBi4True);
  endfunction : mubi4_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_and_hi(mubi4_e a, mubi4_e b);
    return mubi4_and(a, b, MuBi4True);
  endfunction : mubi4_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_or_lo(mubi4_e a, mubi4_e b);
    return mubi4_or(a, b, MuBi4False);
  endfunction : mubi4_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_and_lo(mubi4_e a, mubi4_e b);
    return mubi4_and(a, b, MuBi4False);
  endfunction : mubi4_and_lo

  //////////////////////////////////////////////
  // 8 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi8Width = 8;
  typedef enum logic [MuBi8Width-1:0] {
    MuBi8True = 8'h5A, // enabled
    MuBi8False = 8'hA5  // disabled
  } mubi8_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi8_e mubi8_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi8_e mubi8_true_value();
    return MuBi8True;
  endfunction : mubi8_true_value

  // Return the multibit value to signal "disabled".
  function automatic mubi8_e mubi8_false_value();
    return MuBi8False;
  endfunction : mubi8_false_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi8_test_true_strict(mubi8_e val);
    return MuBi8True == val;
  endfunction : mubi8_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi8_test_false_strict(mubi8_e val);
    return MuBi8False == val;
  endfunction : mubi8_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi8_test_true_loose(mubi8_e val);
    return MuBi8False != val;
  endfunction : mubi8_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi8_test_false_loose(mubi8_e val);
    return MuBi8True != val;
  endfunction : mubi8_test_false_loose


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
  function automatic mubi8_e mubi8_or(mubi8_e a, mubi8_e b, mubi8_e act);
    logic [MuBi8Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi8Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi8_e'(out);
  endfunction : mubi8_or

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
  function automatic mubi8_e mubi8_and(mubi8_e a, mubi8_e b, mubi8_e act);
    logic [MuBi8Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi8Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi8_e'(out);
  endfunction : mubi8_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_or_hi(mubi8_e a, mubi8_e b);
    return mubi8_or(a, b, MuBi8True);
  endfunction : mubi8_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_and_hi(mubi8_e a, mubi8_e b);
    return mubi8_and(a, b, MuBi8True);
  endfunction : mubi8_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_or_lo(mubi8_e a, mubi8_e b);
    return mubi8_or(a, b, MuBi8False);
  endfunction : mubi8_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_and_lo(mubi8_e a, mubi8_e b);
    return mubi8_and(a, b, MuBi8False);
  endfunction : mubi8_and_lo

  //////////////////////////////////////////////
  // 12 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi12Width = 12;
  typedef enum logic [MuBi12Width-1:0] {
    MuBi12True = 12'hA5A, // enabled
    MuBi12False = 12'h5A5  // disabled
  } mubi12_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi12_e mubi12_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi12_e mubi12_true_value();
    return MuBi12True;
  endfunction : mubi12_true_value

  // Return the multibit value to signal "disabled".
  function automatic mubi12_e mubi12_false_value();
    return MuBi12False;
  endfunction : mubi12_false_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi12_test_true_strict(mubi12_e val);
    return MuBi12True == val;
  endfunction : mubi12_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi12_test_false_strict(mubi12_e val);
    return MuBi12False == val;
  endfunction : mubi12_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi12_test_true_loose(mubi12_e val);
    return MuBi12False != val;
  endfunction : mubi12_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi12_test_false_loose(mubi12_e val);
    return MuBi12True != val;
  endfunction : mubi12_test_false_loose


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
  function automatic mubi12_e mubi12_or(mubi12_e a, mubi12_e b, mubi12_e act);
    logic [MuBi12Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi12Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi12_e'(out);
  endfunction : mubi12_or

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
  function automatic mubi12_e mubi12_and(mubi12_e a, mubi12_e b, mubi12_e act);
    logic [MuBi12Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi12Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi12_e'(out);
  endfunction : mubi12_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_or_hi(mubi12_e a, mubi12_e b);
    return mubi12_or(a, b, MuBi12True);
  endfunction : mubi12_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_and_hi(mubi12_e a, mubi12_e b);
    return mubi12_and(a, b, MuBi12True);
  endfunction : mubi12_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_or_lo(mubi12_e a, mubi12_e b);
    return mubi12_or(a, b, MuBi12False);
  endfunction : mubi12_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_and_lo(mubi12_e a, mubi12_e b);
    return mubi12_and(a, b, MuBi12False);
  endfunction : mubi12_and_lo

  //////////////////////////////////////////////
  // 16 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi16Width = 16;
  typedef enum logic [MuBi16Width-1:0] {
    MuBi16True = 16'h5A5A, // enabled
    MuBi16False = 16'hA5A5  // disabled
  } mubi16_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi16_e mubi16_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi16_e mubi16_true_value();
    return MuBi16True;
  endfunction : mubi16_true_value

  // Return the multibit value to signal "disabled".
  function automatic mubi16_e mubi16_false_value();
    return MuBi16False;
  endfunction : mubi16_false_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi16_test_true_strict(mubi16_e val);
    return MuBi16True == val;
  endfunction : mubi16_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi16_test_false_strict(mubi16_e val);
    return MuBi16False == val;
  endfunction : mubi16_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi16_test_true_loose(mubi16_e val);
    return MuBi16False != val;
  endfunction : mubi16_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi16_test_false_loose(mubi16_e val);
    return MuBi16True != val;
  endfunction : mubi16_test_false_loose


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
  function automatic mubi16_e mubi16_or(mubi16_e a, mubi16_e b, mubi16_e act);
    logic [MuBi16Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi16Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi16_e'(out);
  endfunction : mubi16_or

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
  function automatic mubi16_e mubi16_and(mubi16_e a, mubi16_e b, mubi16_e act);
    logic [MuBi16Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi16Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi16_e'(out);
  endfunction : mubi16_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_or_hi(mubi16_e a, mubi16_e b);
    return mubi16_or(a, b, MuBi16True);
  endfunction : mubi16_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_and_hi(mubi16_e a, mubi16_e b);
    return mubi16_and(a, b, MuBi16True);
  endfunction : mubi16_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_or_lo(mubi16_e a, mubi16_e b);
    return mubi16_or(a, b, MuBi16False);
  endfunction : mubi16_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_and_lo(mubi16_e a, mubi16_e b);
    return mubi16_and(a, b, MuBi16False);
  endfunction : mubi16_and_lo

endpackage : prim_mubi_pkg
