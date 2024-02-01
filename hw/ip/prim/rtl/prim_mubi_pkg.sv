// Copyright lowRISC contributors (OpenTitan project).
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

  // Test whether the multibit value is one of the valid enumerations
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
  // This treats "False" as logical 1, and all other values are
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

  // Test whether the multibit value is one of the valid enumerations
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
  // This treats "False" as logical 1, and all other values are
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

  // Test whether the multibit value is one of the valid enumerations
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
  // This treats "False" as logical 1, and all other values are
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

  // Test whether the multibit value is one of the valid enumerations
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
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_t mubi16_and_lo(mubi16_t a, mubi16_t b);
    return mubi16_and(a, b, MuBi16False);
  endfunction : mubi16_and_lo

  //////////////////////////////////////////////
  // 20 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi20Width = 20;
  typedef enum logic [MuBi20Width-1:0] {
    MuBi20True = 20'h69696, // enabled
    MuBi20False = 20'h96969  // disabled
  } mubi20_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi20ValsComplementary_A, MuBi20True == ~MuBi20False)

  // Test whether the multibit value is one of the valid enumerations
  function automatic logic mubi20_test_invalid(mubi20_t val);
    return ~(val inside {MuBi20True, MuBi20False});
  endfunction : mubi20_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi20_t mubi20_bool_to_mubi(logic val);
    return (val ? MuBi20True : MuBi20False);
  endfunction : mubi20_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi20_test_true_strict(mubi20_t val);
    return MuBi20True == val;
  endfunction : mubi20_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi20_test_false_strict(mubi20_t val);
    return MuBi20False == val;
  endfunction : mubi20_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi20_test_true_loose(mubi20_t val);
    return MuBi20False != val;
  endfunction : mubi20_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi20_test_false_loose(mubi20_t val);
    return MuBi20True != val;
  endfunction : mubi20_test_false_loose


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
  function automatic mubi20_t mubi20_or(mubi20_t a, mubi20_t b, mubi20_t act);
    logic [MuBi20Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi20Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi20_t'(out);
  endfunction : mubi20_or

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
  function automatic mubi20_t mubi20_and(mubi20_t a, mubi20_t b, mubi20_t act);
    logic [MuBi20Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi20Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi20_t'(out);
  endfunction : mubi20_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi20_t mubi20_or_hi(mubi20_t a, mubi20_t b);
    return mubi20_or(a, b, MuBi20True);
  endfunction : mubi20_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi20_t mubi20_and_hi(mubi20_t a, mubi20_t b);
    return mubi20_and(a, b, MuBi20True);
  endfunction : mubi20_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi20_t mubi20_or_lo(mubi20_t a, mubi20_t b);
    return mubi20_or(a, b, MuBi20False);
  endfunction : mubi20_or_lo

  // Performs a logical AND operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi20_t mubi20_and_lo(mubi20_t a, mubi20_t b);
    return mubi20_and(a, b, MuBi20False);
  endfunction : mubi20_and_lo

  //////////////////////////////////////////////
  // 24 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi24Width = 24;
  typedef enum logic [MuBi24Width-1:0] {
    MuBi24True = 24'h969696, // enabled
    MuBi24False = 24'h696969  // disabled
  } mubi24_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi24ValsComplementary_A, MuBi24True == ~MuBi24False)

  // Test whether the multibit value is one of the valid enumerations
  function automatic logic mubi24_test_invalid(mubi24_t val);
    return ~(val inside {MuBi24True, MuBi24False});
  endfunction : mubi24_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi24_t mubi24_bool_to_mubi(logic val);
    return (val ? MuBi24True : MuBi24False);
  endfunction : mubi24_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi24_test_true_strict(mubi24_t val);
    return MuBi24True == val;
  endfunction : mubi24_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi24_test_false_strict(mubi24_t val);
    return MuBi24False == val;
  endfunction : mubi24_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi24_test_true_loose(mubi24_t val);
    return MuBi24False != val;
  endfunction : mubi24_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi24_test_false_loose(mubi24_t val);
    return MuBi24True != val;
  endfunction : mubi24_test_false_loose


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
  function automatic mubi24_t mubi24_or(mubi24_t a, mubi24_t b, mubi24_t act);
    logic [MuBi24Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi24Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi24_t'(out);
  endfunction : mubi24_or

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
  function automatic mubi24_t mubi24_and(mubi24_t a, mubi24_t b, mubi24_t act);
    logic [MuBi24Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi24Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi24_t'(out);
  endfunction : mubi24_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi24_t mubi24_or_hi(mubi24_t a, mubi24_t b);
    return mubi24_or(a, b, MuBi24True);
  endfunction : mubi24_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi24_t mubi24_and_hi(mubi24_t a, mubi24_t b);
    return mubi24_and(a, b, MuBi24True);
  endfunction : mubi24_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi24_t mubi24_or_lo(mubi24_t a, mubi24_t b);
    return mubi24_or(a, b, MuBi24False);
  endfunction : mubi24_or_lo

  // Performs a logical AND operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi24_t mubi24_and_lo(mubi24_t a, mubi24_t b);
    return mubi24_and(a, b, MuBi24False);
  endfunction : mubi24_and_lo

  //////////////////////////////////////////////
  // 28 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi28Width = 28;
  typedef enum logic [MuBi28Width-1:0] {
    MuBi28True = 28'h6969696, // enabled
    MuBi28False = 28'h9696969  // disabled
  } mubi28_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi28ValsComplementary_A, MuBi28True == ~MuBi28False)

  // Test whether the multibit value is one of the valid enumerations
  function automatic logic mubi28_test_invalid(mubi28_t val);
    return ~(val inside {MuBi28True, MuBi28False});
  endfunction : mubi28_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi28_t mubi28_bool_to_mubi(logic val);
    return (val ? MuBi28True : MuBi28False);
  endfunction : mubi28_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi28_test_true_strict(mubi28_t val);
    return MuBi28True == val;
  endfunction : mubi28_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi28_test_false_strict(mubi28_t val);
    return MuBi28False == val;
  endfunction : mubi28_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi28_test_true_loose(mubi28_t val);
    return MuBi28False != val;
  endfunction : mubi28_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi28_test_false_loose(mubi28_t val);
    return MuBi28True != val;
  endfunction : mubi28_test_false_loose


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
  function automatic mubi28_t mubi28_or(mubi28_t a, mubi28_t b, mubi28_t act);
    logic [MuBi28Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi28Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi28_t'(out);
  endfunction : mubi28_or

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
  function automatic mubi28_t mubi28_and(mubi28_t a, mubi28_t b, mubi28_t act);
    logic [MuBi28Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi28Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi28_t'(out);
  endfunction : mubi28_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi28_t mubi28_or_hi(mubi28_t a, mubi28_t b);
    return mubi28_or(a, b, MuBi28True);
  endfunction : mubi28_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi28_t mubi28_and_hi(mubi28_t a, mubi28_t b);
    return mubi28_and(a, b, MuBi28True);
  endfunction : mubi28_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi28_t mubi28_or_lo(mubi28_t a, mubi28_t b);
    return mubi28_or(a, b, MuBi28False);
  endfunction : mubi28_or_lo

  // Performs a logical AND operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi28_t mubi28_and_lo(mubi28_t a, mubi28_t b);
    return mubi28_and(a, b, MuBi28False);
  endfunction : mubi28_and_lo

  //////////////////////////////////////////////
  // 32 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi32Width = 32;
  typedef enum logic [MuBi32Width-1:0] {
    MuBi32True = 32'h96969696, // enabled
    MuBi32False = 32'h69696969  // disabled
  } mubi32_t;

  // This is a prerequisite for the multibit functions below to work.
  `ASSERT_STATIC_IN_PACKAGE(CheckMuBi32ValsComplementary_A, MuBi32True == ~MuBi32False)

  // Test whether the multibit value is one of the valid enumerations
  function automatic logic mubi32_test_invalid(mubi32_t val);
    return ~(val inside {MuBi32True, MuBi32False});
  endfunction : mubi32_test_invalid

  // Convert a 1 input value to a mubi output
  function automatic mubi32_t mubi32_bool_to_mubi(logic val);
    return (val ? MuBi32True : MuBi32False);
  endfunction : mubi32_bool_to_mubi

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal True.
  function automatic logic mubi32_test_true_strict(mubi32_t val);
    return MuBi32True == val;
  endfunction : mubi32_test_true_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal False.
  function automatic logic mubi32_test_false_strict(mubi32_t val);
    return MuBi32False == val;
  endfunction : mubi32_test_false_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than False as "enabled".
  function automatic logic mubi32_test_true_loose(mubi32_t val);
    return MuBi32False != val;
  endfunction : mubi32_test_true_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than True as "disabled".
  function automatic logic mubi32_test_false_loose(mubi32_t val);
    return MuBi32True != val;
  endfunction : mubi32_test_false_loose


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
  function automatic mubi32_t mubi32_or(mubi32_t a, mubi32_t b, mubi32_t act);
    logic [MuBi32Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi32Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] || b_in[k];
      end else begin
        out[k] = a_in[k] && b_in[k];
      end
    end
    return mubi32_t'(out);
  endfunction : mubi32_or

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
  function automatic mubi32_t mubi32_and(mubi32_t a, mubi32_t b, mubi32_t act);
    logic [MuBi32Width-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    act_in = act;
    for (int k = 0; k < MuBi32Width; k++) begin
      if (act_in[k]) begin
        out[k] = a_in[k] && b_in[k];
      end else begin
        out[k] = a_in[k] || b_in[k];
      end
    end
    return mubi32_t'(out);
  endfunction : mubi32_and

  // Performs a logical OR operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi32_t mubi32_or_hi(mubi32_t a, mubi32_t b);
    return mubi32_or(a, b, MuBi32True);
  endfunction : mubi32_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "True" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi32_t mubi32_and_hi(mubi32_t a, mubi32_t b);
    return mubi32_and(a, b, MuBi32True);
  endfunction : mubi32_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi32_t mubi32_or_lo(mubi32_t a, mubi32_t b);
    return mubi32_or(a, b, MuBi32False);
  endfunction : mubi32_or_lo

  // Performs a logical AND operation between two multibit values.
  // This treats "False" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi32_t mubi32_and_lo(mubi32_t a, mubi32_t b);
    return mubi32_and(a, b, MuBi32False);
  endfunction : mubi32_and_lo

endpackage : prim_mubi_pkg
