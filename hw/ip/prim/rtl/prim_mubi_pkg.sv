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

  //////////////////////////////////////////////
  // 4 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi4Width = 4;
  typedef enum logic [MuBi4Width-1:0] {
    MuBi4Hi = 4'h5, // enabled
    MuBi4Lo = 4'hA  // disabled
  } mubi4_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi4_e mubi4_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi4_e mubi4_hi_value();
    return MuBi4Hi;
  endfunction : mubi4_hi_value

  // Return the multibit value to signal "disabled".
  function automatic mubi4_e mubi4_lo_value();
    return MuBi4Lo;
  endfunction : mubi4_lo_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Hi.
  function automatic logic mubi4_tst_hi_strict(mubi4_e val);
    return MuBi4Hi == val;
  endfunction : mubi4_tst_hi_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Lo.
  function automatic logic mubi4_tst_lo_strict(mubi4_e val);
    return MuBi4Lo == val;
  endfunction : mubi4_tst_lo_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than Lo as "enabled".
  function automatic logic mubi4_tst_hi_loose(mubi4_e val);
    return MuBi4Lo != val;
  endfunction : mubi4_tst_hi_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than Hi as "disabled".
  function automatic logic mubi4_tst_lo_loose(mubi4_e val);
    return MuBi4Hi != val;
  endfunction : mubi4_tst_lo_loose


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
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_or_hi(mubi4_e a, mubi4_e b);
    return mubi4_or(a, b, MuBi4Hi);
  endfunction : mubi4_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_and_hi(mubi4_e a, mubi4_e b);
    return mubi4_and(a, b, MuBi4Hi);
  endfunction : mubi4_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_or_lo(mubi4_e a, mubi4_e b);
    return mubi4_or(a, b, MuBi4Lo);
  endfunction : mubi4_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi4_e mubi4_and_lo(mubi4_e a, mubi4_e b);
    return mubi4_and(a, b, MuBi4Lo);
  endfunction : mubi4_and_lo

  //////////////////////////////////////////////
  // 8 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi8Width = 8;
  typedef enum logic [MuBi8Width-1:0] {
    MuBi8Hi = 8'hA5, // enabled
    MuBi8Lo = 8'h5A  // disabled
  } mubi8_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi8_e mubi8_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi8_e mubi8_hi_value();
    return MuBi8Hi;
  endfunction : mubi8_hi_value

  // Return the multibit value to signal "disabled".
  function automatic mubi8_e mubi8_lo_value();
    return MuBi8Lo;
  endfunction : mubi8_lo_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Hi.
  function automatic logic mubi8_tst_hi_strict(mubi8_e val);
    return MuBi8Hi == val;
  endfunction : mubi8_tst_hi_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Lo.
  function automatic logic mubi8_tst_lo_strict(mubi8_e val);
    return MuBi8Lo == val;
  endfunction : mubi8_tst_lo_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than Lo as "enabled".
  function automatic logic mubi8_tst_hi_loose(mubi8_e val);
    return MuBi8Lo != val;
  endfunction : mubi8_tst_hi_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than Hi as "disabled".
  function automatic logic mubi8_tst_lo_loose(mubi8_e val);
    return MuBi8Hi != val;
  endfunction : mubi8_tst_lo_loose


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
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_or_hi(mubi8_e a, mubi8_e b);
    return mubi8_or(a, b, MuBi8Hi);
  endfunction : mubi8_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_and_hi(mubi8_e a, mubi8_e b);
    return mubi8_and(a, b, MuBi8Hi);
  endfunction : mubi8_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_or_lo(mubi8_e a, mubi8_e b);
    return mubi8_or(a, b, MuBi8Lo);
  endfunction : mubi8_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi8_e mubi8_and_lo(mubi8_e a, mubi8_e b);
    return mubi8_and(a, b, MuBi8Lo);
  endfunction : mubi8_and_lo

  //////////////////////////////////////////////
  // 12 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi12Width = 12;
  typedef enum logic [MuBi12Width-1:0] {
    MuBi12Hi = 12'h5A5, // enabled
    MuBi12Lo = 12'hA5A  // disabled
  } mubi12_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi12_e mubi12_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi12_e mubi12_hi_value();
    return MuBi12Hi;
  endfunction : mubi12_hi_value

  // Return the multibit value to signal "disabled".
  function automatic mubi12_e mubi12_lo_value();
    return MuBi12Lo;
  endfunction : mubi12_lo_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Hi.
  function automatic logic mubi12_tst_hi_strict(mubi12_e val);
    return MuBi12Hi == val;
  endfunction : mubi12_tst_hi_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Lo.
  function automatic logic mubi12_tst_lo_strict(mubi12_e val);
    return MuBi12Lo == val;
  endfunction : mubi12_tst_lo_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than Lo as "enabled".
  function automatic logic mubi12_tst_hi_loose(mubi12_e val);
    return MuBi12Lo != val;
  endfunction : mubi12_tst_hi_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than Hi as "disabled".
  function automatic logic mubi12_tst_lo_loose(mubi12_e val);
    return MuBi12Hi != val;
  endfunction : mubi12_tst_lo_loose


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
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_or_hi(mubi12_e a, mubi12_e b);
    return mubi12_or(a, b, MuBi12Hi);
  endfunction : mubi12_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_and_hi(mubi12_e a, mubi12_e b);
    return mubi12_and(a, b, MuBi12Hi);
  endfunction : mubi12_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_or_lo(mubi12_e a, mubi12_e b);
    return mubi12_or(a, b, MuBi12Lo);
  endfunction : mubi12_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi12_e mubi12_and_lo(mubi12_e a, mubi12_e b);
    return mubi12_and(a, b, MuBi12Lo);
  endfunction : mubi12_and_lo

  //////////////////////////////////////////////
  // 16 Bit Multibit Type and Functions //
  //////////////////////////////////////////////

  parameter int MuBi16Width = 16;
  typedef enum logic [MuBi16Width-1:0] {
    MuBi16Hi = 16'hA5A5, // enabled
    MuBi16Lo = 16'h5A5A  // disabled
  } mubi16_e;

  // make a typedef such that this can be used as an intersignal type as well
  typedef mubi16_e mubi16_t;

  // Return the multibit value to signal "enabled".
  function automatic mubi16_e mubi16_hi_value();
    return MuBi16Hi;
  endfunction : mubi16_hi_value

  // Return the multibit value to signal "disabled".
  function automatic mubi16_e mubi16_lo_value();
    return MuBi16Lo;
  endfunction : mubi16_lo_value

  // Test whether the multibit value signals an "enabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Hi.
  function automatic logic mubi16_tst_hi_strict(mubi16_e val);
    return MuBi16Hi == val;
  endfunction : mubi16_tst_hi_strict

  // Test whether the multibit value signals a "disabled" condition.
  // The strict version of this function requires
  // the multibit value to equal Lo.
  function automatic logic mubi16_tst_lo_strict(mubi16_e val);
    return MuBi16Lo == val;
  endfunction : mubi16_tst_lo_strict

  // Test whether the multibit value signals an "enabled" condition.
  // The loose version of this function interprets all
  // values other than Lo as "enabled".
  function automatic logic mubi16_tst_hi_loose(mubi16_e val);
    return MuBi16Lo != val;
  endfunction : mubi16_tst_hi_loose

  // Test whether the multibit value signals a "disabled" condition.
  // The loose version of this function interprets all
  // values other than Hi as "disabled".
  function automatic logic mubi16_tst_lo_loose(mubi16_e val);
    return MuBi16Hi != val;
  endfunction : mubi16_tst_lo_loose


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
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_or_hi(mubi16_e a, mubi16_e b);
    return mubi16_or(a, b, MuBi16Hi);
  endfunction : mubi16_or_hi

  // Performs a logical AND operation between two multibit values.
  // This treats "Hi" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_and_hi(mubi16_e a, mubi16_e b);
    return mubi16_and(a, b, MuBi16Hi);
  endfunction : mubi16_and_hi

  // Performs a logical OR operation between two multibit values.
  // This treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_or_lo(mubi16_e a, mubi16_e b);
    return mubi16_or(a, b, MuBi16Lo);
  endfunction : mubi16_or_lo

  // Performs a logical AND operation between two multibit values.
  // Tlos treats "Lo" as logical 1, and all other values are
  // treated as 0.
  function automatic mubi16_e mubi16_and_lo(mubi16_e a, mubi16_e b);
    return mubi16_and(a, b, MuBi16Lo);
  endfunction : mubi16_and_lo

endpackage : prim_mubi_pkg

