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

`include "prim_assert.sv"

package prim_mubi_pkg;

  //////////////////////////////////////////////
  // 4 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi4Width = 4;
  typedef enum logic [MuBi4Width-1:0] {
    MuBi4True = 4'h6, // enabled
    MuBi4False = 4'h9  // disabled
  } mubi4_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi4ValsComplementary_A, MuBi4True == ~MuBi4False)

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic mubi4_test_invalid(mubi4_t val);
    return ~(val inside {MuBi4True, MuBi4False});
  endfunction : mubi4_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi4_t mubi4_bool_to_mubi(logic val);
    return (val ? MuBi4True : MuBi4False);
  endfunction : mubi4_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi4_test_true_strict(mubi4_t val);
    return MuBi4True == val;
  endfunction : mubi4_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi4_test_false_strict(mubi4_t val);
    return MuBi4False == val;
  endfunction : mubi4_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi4_test_true_loose(mubi4_t val);
    return MuBi4False != val;
  endfunction : mubi4_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi4_test_false_loose(mubi4_t val);
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
  function automatic mubi4_t mubi4_or(mubi4_t a, mubi4_t b, mubi4_t act);
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
    return mubi4_t'(out);
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
  function automatic mubi4_t mubi4_and(mubi4_t a, mubi4_t b, mubi4_t act);
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
    return mubi4_t'(out);
  endfunction : mubi4_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_t mubi4_or_hi(mubi4_t a, mubi4_t b);
    return mubi4_or(a, b, MuBi4True);
  endfunction : mubi4_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_t mubi4_and_hi(mubi4_t a, mubi4_t b);
    return mubi4_and(a, b, MuBi4True);
  endfunction : mubi4_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_t mubi4_or_lo(mubi4_t a, mubi4_t b);
    return mubi4_or(a, b, MuBi4False);
  endfunction : mubi4_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_t mubi4_and_lo(mubi4_t a, mubi4_t b);
    return mubi4_and(a, b, MuBi4False);
  endfunction : mubi4_and_lo

  //////////////////////////////////////////////
  // 8 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi8Width = 8;
  typedef enum logic [MuBi8Width-1:0] {
    MuBi8True = 8'h96, // enabled
    MuBi8False = 8'h69  // disabled
  } mubi8_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi8ValsComplementary_A, MuBi8True == ~MuBi8False)

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic mubi8_test_invalid(mubi8_t val);
    return ~(val inside {MuBi8True, MuBi8False});
  endfunction : mubi8_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi8_t mubi8_bool_to_mubi(logic val);
    return (val ? MuBi8True : MuBi8False);
  endfunction : mubi8_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi8_test_true_strict(mubi8_t val);
    return MuBi8True == val;
  endfunction : mubi8_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi8_test_false_strict(mubi8_t val);
    return MuBi8False == val;
  endfunction : mubi8_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi8_test_true_loose(mubi8_t val);
    return MuBi8False != val;
  endfunction : mubi8_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi8_test_false_loose(mubi8_t val);
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
  function automatic mubi8_t mubi8_or(mubi8_t a, mubi8_t b, mubi8_t act);
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
    return mubi8_t'(out);
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
  function automatic mubi8_t mubi8_and(mubi8_t a, mubi8_t b, mubi8_t act);
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
    return mubi8_t'(out);
  endfunction : mubi8_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_t mubi8_or_hi(mubi8_t a, mubi8_t b);
    return mubi8_or(a, b, MuBi8True);
  endfunction : mubi8_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_t mubi8_and_hi(mubi8_t a, mubi8_t b);
    return mubi8_and(a, b, MuBi8True);
  endfunction : mubi8_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_t mubi8_or_lo(mubi8_t a, mubi8_t b);
    return mubi8_or(a, b, MuBi8False);
  endfunction : mubi8_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_t mubi8_and_lo(mubi8_t a, mubi8_t b);
    return mubi8_and(a, b, MuBi8False);
  endfunction : mubi8_and_lo

  //////////////////////////////////////////////
  // 12 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi12Width = 12;
  typedef enum logic [MuBi12Width-1:0] {
    MuBi12True = 12'h696, // enabled
    MuBi12False = 12'h969  // disabled
  } mubi12_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi12ValsComplementary_A, MuBi12True == ~MuBi12False)

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic mubi12_test_invalid(mubi12_t val);
    return ~(val inside {MuBi12True, MuBi12False});
  endfunction : mubi12_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi12_t mubi12_bool_to_mubi(logic val);
    return (val ? MuBi12True : MuBi12False);
  endfunction : mubi12_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi12_test_true_strict(mubi12_t val);
    return MuBi12True == val;
  endfunction : mubi12_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi12_test_false_strict(mubi12_t val);
    return MuBi12False == val;
  endfunction : mubi12_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi12_test_true_loose(mubi12_t val);
    return MuBi12False != val;
  endfunction : mubi12_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi12_test_false_loose(mubi12_t val);
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
  function automatic mubi12_t mubi12_or(mubi12_t a, mubi12_t b, mubi12_t act);
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
    return mubi12_t'(out);
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
  function automatic mubi12_t mubi12_and(mubi12_t a, mubi12_t b, mubi12_t act);
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
    return mubi12_t'(out);
  endfunction : mubi12_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_t mubi12_or_hi(mubi12_t a, mubi12_t b);
    return mubi12_or(a, b, MuBi12True);
  endfunction : mubi12_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_t mubi12_and_hi(mubi12_t a, mubi12_t b);
    return mubi12_and(a, b, MuBi12True);
  endfunction : mubi12_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_t mubi12_or_lo(mubi12_t a, mubi12_t b);
    return mubi12_or(a, b, MuBi12False);
  endfunction : mubi12_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_t mubi12_and_lo(mubi12_t a, mubi12_t b);
    return mubi12_and(a, b, MuBi12False);
  endfunction : mubi12_and_lo

  //////////////////////////////////////////////
  // 16 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi16Width = 16;
  typedef enum logic [MuBi16Width-1:0] {
    MuBi16True = 16'h9696, // enabled
    MuBi16False = 16'h6969  // disabled
  } mubi16_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi16ValsComplementary_A, MuBi16True == ~MuBi16False)

  // Test whether the value is supplied is one of the valid enumerations
  function automatic logic mubi16_test_invalid(mubi16_t val);
    return ~(val inside {MuBi16True, MuBi16False});
  endfunction : mubi16_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi16_t mubi16_bool_to_mubi(logic val);
    return (val ? MuBi16True : MuBi16False);
  endfunction : mubi16_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi16_test_true_strict(mubi16_t val);
    return MuBi16True == val;
  endfunction : mubi16_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi16_test_false_strict(mubi16_t val);
    return MuBi16False == val;
  endfunction : mubi16_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi16_test_true_loose(mubi16_t val);
    return MuBi16False != val;
  endfunction : mubi16_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi16_test_false_loose(mubi16_t val);
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
  function automatic mubi16_t mubi16_or(mubi16_t a, mubi16_t b, mubi16_t act);
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
    return mubi16_t'(out);
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
  function automatic mubi16_t mubi16_and(mubi16_t a, mubi16_t b, mubi16_t act);
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
    return mubi16_t'(out);
  endfunction : mubi16_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_t mubi16_or_hi(mubi16_t a, mubi16_t b);
    return mubi16_or(a, b, MuBi16True);
  endfunction : mubi16_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_t mubi16_and_hi(mubi16_t a, mubi16_t b);
    return mubi16_and(a, b, MuBi16True);
  endfunction : mubi16_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_t mubi16_or_lo(mubi16_t a, mubi16_t b);
    return mubi16_or(a, b, MuBi16False);
  endfunction : mubi16_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_t mubi16_and_lo(mubi16_t a, mubi16_t b);
    return mubi16_and(a, b, MuBi16False);
  endfunction : mubi16_and_lo

endpackage : prim_mubi_pkg
