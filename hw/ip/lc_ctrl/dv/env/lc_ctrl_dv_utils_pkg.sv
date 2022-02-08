// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package lc_ctrl_dv_utils_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;

  // associative array cannot declare parameter here, so we used const instead
  // verilog_format: off - avoid bad formatting
  const dec_lc_state_e VALID_NEXT_STATES [dec_lc_state_e][$] = '{
    DecLcStRma:     {DecLcStScrap},
    DecLcStProdEnd: {DecLcStScrap},
    DecLcStProd:    {DecLcStScrap, DecLcStRma},
    DecLcStDev:     {DecLcStScrap, DecLcStRma},
    DecLcStTestUnlocked7: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev},
    DecLcStTestUnlocked6: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6},
    DecLcStTestUnlocked5: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5},
    DecLcStTestUnlocked4: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5, DecLcStTestLocked4},
    DecLcStTestUnlocked3: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5, DecLcStTestLocked4,
                           DecLcStTestLocked3},
    DecLcStTestUnlocked2: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5, DecLcStTestLocked4,
                           DecLcStTestLocked3, DecLcStTestLocked2},
    DecLcStTestUnlocked1: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5, DecLcStTestLocked4,
                           DecLcStTestLocked3, DecLcStTestLocked2, DecLcStTestLocked1},
    DecLcStTestUnlocked0: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked6, DecLcStTestLocked5, DecLcStTestLocked4,
                           DecLcStTestLocked3, DecLcStTestLocked2, DecLcStTestLocked1,
                           DecLcStTestLocked0},
    DecLcStTestLocked6: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7},
    DecLcStTestLocked5: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6},
    DecLcStTestLocked4: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5},
    DecLcStTestLocked3: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5,
                         DecLcStTestUnlocked4},
    DecLcStTestLocked2: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5,
                         DecLcStTestUnlocked4, DecLcStTestUnlocked3},
    DecLcStTestLocked1: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5,
                         DecLcStTestUnlocked4, DecLcStTestUnlocked3, DecLcStTestUnlocked2},
    DecLcStTestLocked0: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5,
                         DecLcStTestUnlocked4, DecLcStTestUnlocked3, DecLcStTestUnlocked2,
                         DecLcStTestUnlocked1},
    DecLcStRaw: {DecLcStScrap, DecLcStTestUnlocked7, DecLcStTestUnlocked6, DecLcStTestUnlocked5,
                 DecLcStTestUnlocked4, DecLcStTestUnlocked3, DecLcStTestUnlocked2,
                 DecLcStTestUnlocked1, DecLcStTestUnlocked0}
  };


  // All valid decoded states as int
  const int ValidDecodedStates[] = '{
    int'(DecLcStRaw),
    int'(DecLcStTestUnlocked0),
    int'(DecLcStTestLocked0),
    int'(DecLcStTestUnlocked1),
    int'(DecLcStTestLocked1),
    int'(DecLcStTestUnlocked2),
    int'(DecLcStTestLocked2),
    int'(DecLcStTestUnlocked3),
    int'(DecLcStTestLocked3),
    int'(DecLcStTestUnlocked4),
    int'(DecLcStTestLocked4),
    int'(DecLcStTestUnlocked5),
    int'(DecLcStTestLocked5),
    int'(DecLcStTestUnlocked6),
    int'(DecLcStTestLocked6),
    int'(DecLcStTestUnlocked7),
    int'(DecLcStDev),
    int'(DecLcStProd),
    int'(DecLcStProdEnd),
    int'(DecLcStRma),
    int'(DecLcStScrap),
    int'(DecLcStInvalid)
  };

  // Checks whether the current state is a test unlocked state within the given index range.
  function automatic bit is_test_unlocked_state(dec_lc_state_e curr_state, int first, int last);
  begin
    int index;
    index = (curr_state - DecLcStTestUnlocked0)/2;
    case (curr_state)
      DecLcStTestUnlocked0,
      DecLcStTestUnlocked1,
      DecLcStTestUnlocked2,
      DecLcStTestUnlocked3,
      DecLcStTestUnlocked4,
      DecLcStTestUnlocked5,
      DecLcStTestUnlocked6,
      DecLcStTestUnlocked7: return (index >= first) && (index <= last);
      default: return 0;
    endcase
  end
  endfunction

  // Checks whether the current state is a test locked state within the given index range.
  function automatic bit is_test_locked_state(dec_lc_state_e curr_state, int first, int last);
  begin
    int index;
    index = (curr_state - DecLcStTestLocked0)/2;
    case (curr_state)
      DecLcStTestLocked0,
      DecLcStTestLocked1,
      DecLcStTestLocked2,
      DecLcStTestLocked3,
      DecLcStTestLocked4,
      DecLcStTestLocked5,
      DecLcStTestLocked6: return (index >= first) && (index <= last);
      default: return 0;
    endcase
  end
  endfunction
  // verilog_format: on

  function automatic dec_lc_state_e dec_lc_state(lc_state_e curr_state);
    case (curr_state)
      LcStRaw:           return DecLcStRaw;
      LcStTestUnlocked0: return DecLcStTestUnlocked0;
      LcStTestLocked0:   return DecLcStTestLocked0;
      LcStTestUnlocked1: return DecLcStTestUnlocked1;
      LcStTestLocked1:   return DecLcStTestLocked1;
      LcStTestUnlocked2: return DecLcStTestUnlocked2;
      LcStTestLocked2:   return DecLcStTestLocked2;
      LcStTestUnlocked3: return DecLcStTestUnlocked3;
      LcStTestLocked3:   return DecLcStTestLocked3;
      LcStTestUnlocked4: return DecLcStTestUnlocked4;
      LcStTestLocked4:   return DecLcStTestLocked4;
      LcStTestUnlocked5: return DecLcStTestUnlocked5;
      LcStTestLocked5:   return DecLcStTestLocked5;
      LcStTestUnlocked6: return DecLcStTestUnlocked6;
      LcStTestLocked6:   return DecLcStTestLocked6;
      LcStTestUnlocked7: return DecLcStTestUnlocked7;
      LcStDev:           return DecLcStDev;
      LcStProd:          return DecLcStProd;
      LcStProdEnd:       return DecLcStProdEnd;
      LcStRma:           return DecLcStRma;
      LcStScrap:         return DecLcStScrap;
      default:           return DecLcStInvalid;
    endcase
  endfunction

  function automatic lc_state_e encode_lc_state(dec_lc_state_e curr_state);
    case (curr_state)
      DecLcStRaw: return LcStRaw;
      DecLcStTestUnlocked0: return LcStTestUnlocked0;
      DecLcStTestLocked0: return LcStTestLocked0;
      DecLcStTestUnlocked1: return LcStTestUnlocked1;
      DecLcStTestLocked1: return LcStTestLocked1;
      DecLcStTestUnlocked2: return LcStTestUnlocked2;
      DecLcStTestLocked2: return LcStTestLocked2;
      DecLcStTestUnlocked3: return LcStTestUnlocked3;
      DecLcStTestLocked3: return LcStTestLocked3;
      DecLcStTestUnlocked4: return LcStTestUnlocked4;
      DecLcStTestLocked4: return LcStTestLocked4;
      DecLcStTestUnlocked5: return LcStTestUnlocked5;
      DecLcStTestLocked5: return LcStTestLocked5;
      DecLcStTestUnlocked6: return LcStTestUnlocked6;
      DecLcStTestLocked6: return LcStTestLocked6;
      DecLcStTestUnlocked7: return LcStTestUnlocked7;
      DecLcStDev: return LcStDev;
      DecLcStProd: return LcStProd;
      DecLcStProdEnd: return LcStProdEnd;
      DecLcStRma: return LcStRma;
      DecLcStScrap: return LcStScrap;
      default: begin
        `uvm_fatal("lc_env_pkg", $sformatf("encode_lc_state: unknown lc_state 0x%0h", curr_state))
      end
    endcase
  endfunction

  function automatic int dec_lc_cnt(lc_cnt_e curr_cnt);
    case (curr_cnt)
      LcCnt0:  return 0;
      LcCnt1:  return 1;
      LcCnt2:  return 2;
      LcCnt3:  return 3;
      LcCnt4:  return 4;
      LcCnt5:  return 5;
      LcCnt6:  return 6;
      LcCnt7:  return 7;
      LcCnt8:  return 8;
      LcCnt9:  return 9;
      LcCnt10: return 10;
      LcCnt11: return 11;
      LcCnt12: return 12;
      LcCnt13: return 13;
      LcCnt14: return 14;
      LcCnt15: return 15;
      LcCnt16: return 16;
      LcCnt17: return 17;
      LcCnt18: return 18;
      LcCnt19: return 19;
      LcCnt20: return 20;
      LcCnt21: return 21;
      LcCnt22: return 22;
      LcCnt23: return 23;
      LcCnt24: return 24;
      default: `uvm_fatal("lc_env_pkg", $sformatf("dec_lc_cnt: unknown lc_cnt 0x%0h", curr_cnt))
    endcase
  endfunction

  // Arrays of digit values
  parameter bit [15:0] A_VALUES[20] = '{
      lc_ctrl_state_pkg::A0,
      lc_ctrl_state_pkg::A1,
      lc_ctrl_state_pkg::A2,
      lc_ctrl_state_pkg::A3,
      lc_ctrl_state_pkg::A4,
      lc_ctrl_state_pkg::A5,
      lc_ctrl_state_pkg::A6,
      lc_ctrl_state_pkg::A7,
      lc_ctrl_state_pkg::A8,
      lc_ctrl_state_pkg::A9,
      lc_ctrl_state_pkg::A10,
      lc_ctrl_state_pkg::A11,
      lc_ctrl_state_pkg::A12,
      lc_ctrl_state_pkg::A13,
      lc_ctrl_state_pkg::A14,
      lc_ctrl_state_pkg::A15,
      lc_ctrl_state_pkg::A16,
      lc_ctrl_state_pkg::A17,
      lc_ctrl_state_pkg::A18,
      lc_ctrl_state_pkg::A19
  };

  parameter bit [15:0] B_VALUES[20] = '{
      lc_ctrl_state_pkg::B0,
      lc_ctrl_state_pkg::B1,
      lc_ctrl_state_pkg::B2,
      lc_ctrl_state_pkg::B3,
      lc_ctrl_state_pkg::B4,
      lc_ctrl_state_pkg::B5,
      lc_ctrl_state_pkg::B6,
      lc_ctrl_state_pkg::B7,
      lc_ctrl_state_pkg::B8,
      lc_ctrl_state_pkg::B9,
      lc_ctrl_state_pkg::B10,
      lc_ctrl_state_pkg::B11,
      lc_ctrl_state_pkg::B12,
      lc_ctrl_state_pkg::B13,
      lc_ctrl_state_pkg::B14,
      lc_ctrl_state_pkg::B15,
      lc_ctrl_state_pkg::B16,
      lc_ctrl_state_pkg::B17,
      lc_ctrl_state_pkg::B18,
      lc_ctrl_state_pkg::B19
  };

  parameter bit [15:0] C_VALUES[24] = '{
      lc_ctrl_state_pkg::C0,
      lc_ctrl_state_pkg::C1,
      lc_ctrl_state_pkg::C2,
      lc_ctrl_state_pkg::C3,
      lc_ctrl_state_pkg::C4,
      lc_ctrl_state_pkg::C5,
      lc_ctrl_state_pkg::C6,
      lc_ctrl_state_pkg::C7,
      lc_ctrl_state_pkg::C8,
      lc_ctrl_state_pkg::C9,
      lc_ctrl_state_pkg::C10,
      lc_ctrl_state_pkg::C11,
      lc_ctrl_state_pkg::C12,
      lc_ctrl_state_pkg::C13,
      lc_ctrl_state_pkg::C14,
      lc_ctrl_state_pkg::C15,
      lc_ctrl_state_pkg::C16,
      lc_ctrl_state_pkg::C17,
      lc_ctrl_state_pkg::C18,
      lc_ctrl_state_pkg::C19,
      lc_ctrl_state_pkg::C20,
      lc_ctrl_state_pkg::C21,
      lc_ctrl_state_pkg::C22,
      lc_ctrl_state_pkg::C23
  };

  parameter bit [15:0] D_VALUES[24] = '{
      lc_ctrl_state_pkg::D0,
      lc_ctrl_state_pkg::D1,
      lc_ctrl_state_pkg::D2,
      lc_ctrl_state_pkg::D3,
      lc_ctrl_state_pkg::D4,
      lc_ctrl_state_pkg::D5,
      lc_ctrl_state_pkg::D6,
      lc_ctrl_state_pkg::D7,
      lc_ctrl_state_pkg::D8,
      lc_ctrl_state_pkg::D9,
      lc_ctrl_state_pkg::D10,
      lc_ctrl_state_pkg::D11,
      lc_ctrl_state_pkg::D12,
      lc_ctrl_state_pkg::D13,
      lc_ctrl_state_pkg::D14,
      lc_ctrl_state_pkg::D15,
      lc_ctrl_state_pkg::D16,
      lc_ctrl_state_pkg::D17,
      lc_ctrl_state_pkg::D18,
      lc_ctrl_state_pkg::D19,
      lc_ctrl_state_pkg::D20,
      lc_ctrl_state_pkg::D21,
      lc_ctrl_state_pkg::D22,
      lc_ctrl_state_pkg::D23
  };

  // Binary representation of state and count types
  typedef bit [NumLcStateValues - 1 : 0] lc_state_bin_t;
  typedef bit [NumLcCountValues - 1 : 0] lc_count_bin_t;



  //Convert an lc_state to a binary representation 0=Axx 1=Bxx
  function static lc_state_bin_t lc_state_to_bin(bit [LcStateWidth-1:0] val);
    lc_state_to_bin = 0;
    for (int i = 0; i < $size(A_VALUES); i++) begin
      if (val[i*16+:16] == A_VALUES[i]) begin
        lc_state_to_bin[i] = 0;
      end else if (val[i*16+:16] == B_VALUES[i]) begin
        lc_state_to_bin[i] = 1;
      end else begin
        $fatal(0, "lc_ctrl_dv_utils_pkg lc_state_to_bin: state %x not valid", val);
      end
    end
  endfunction

  //Convert a binary representation to a lc_state representation 0=Axx 1=Bxx
  function static bit [LcStateWidth-1:0] bin_to_lc_state(lc_state_bin_t val, bit err_inj = 0);
    int err_inj_idx = -1;
    bin_to_lc_state = 0;
    if (err_inj) begin
      // Select a symbol to invert
      err_inj_idx = $urandom_range(0, $size(A_VALUES) - 1);
    end
    for (int i = 0; i < $size(A_VALUES); i++) begin
      if (i != err_inj_idx) begin
        // No error
        bin_to_lc_state[i*16+:16] = val[i] ? B_VALUES[i] : A_VALUES[i];
      end else begin
        // Error inject - invert symbol
        bin_to_lc_state[i*16+:16] = val[i] ? ~B_VALUES[i] : ~A_VALUES[i];
      end
    end
  endfunction

  //Convert an lc_count to a binary representation 0=Cxx 1=Dxx
  function static lc_count_bin_t lc_count_to_bin(bit [LcCountWidth-1:0] val);
    lc_count_to_bin = 0;
    for (int i = 0; i < $size(C_VALUES); i++) begin
      if (val[i*16+:16] == C_VALUES[i]) begin
        lc_count_to_bin[i] = 0;
      end else if (val[i*16+:16] == D_VALUES[i]) begin
        lc_count_to_bin[i] = 1;
      end else begin
        $fatal(0, "lc_ctrl_dv_utils_pkg lc_count_to_bin: count %x not valid", val);
      end
    end
  endfunction

  //Convert a binary representation to a lc_count representation 0=Cxx 1=Dxx
  function static bit [LcCountWidth-1:0] bin_to_lc_count(lc_count_bin_t val, bit err_inj = 0);
    int err_inj_idx = -1;
    bin_to_lc_count = 0;
    if (err_inj) begin
      // Select a symbol to invert
      err_inj_idx = $urandom_range(0, $size(C_VALUES) - 1);
    end
    for (int i = 0; i < $size(C_VALUES); i++) begin
      if (i != err_inj_idx) begin
        // No error
        bin_to_lc_count[i*16+:16] = val[i] ? D_VALUES[i] : C_VALUES[i];
      end else begin
        // Error inject - invert symbol
        bin_to_lc_count[i*16+:16] = val[i] ? ~D_VALUES[i] : ~C_VALUES[i];
      end
    end
  endfunction

  // Array of valid LC states in binary representation
  parameter lc_state_bin_t ValidLcStatesBin[NumLcStates] = '{
      lc_state_to_bin(LcStRaw),
      lc_state_to_bin(LcStTestUnlocked0),
      lc_state_to_bin(LcStTestLocked0),
      lc_state_to_bin(LcStTestUnlocked1),
      lc_state_to_bin(LcStTestLocked1),
      lc_state_to_bin(LcStTestUnlocked2),
      lc_state_to_bin(LcStTestLocked2),
      lc_state_to_bin(LcStTestUnlocked3),
      lc_state_to_bin(LcStTestLocked3),
      lc_state_to_bin(LcStTestUnlocked4),
      lc_state_to_bin(LcStTestLocked4),
      lc_state_to_bin(LcStTestUnlocked5),
      lc_state_to_bin(LcStTestLocked5),
      lc_state_to_bin(LcStTestUnlocked6),
      lc_state_to_bin(LcStTestLocked6),
      lc_state_to_bin(LcStTestUnlocked7),
      lc_state_to_bin(LcStDev),
      lc_state_to_bin(LcStProd),
      lc_state_to_bin(LcStProdEnd),
      lc_state_to_bin(LcStRma),
      lc_state_to_bin(LcStScrap)
  };

  // Array of valid LC states in binary representation
  parameter lc_count_bin_t ValidLcCountsBin[NumLcCountStates] = '{
      lc_count_to_bin(LcCnt0),
      lc_count_to_bin(LcCnt1),
      lc_count_to_bin(LcCnt2),
      lc_count_to_bin(LcCnt3),
      lc_count_to_bin(LcCnt4),
      lc_count_to_bin(LcCnt5),
      lc_count_to_bin(LcCnt6),
      lc_count_to_bin(LcCnt7),
      lc_count_to_bin(LcCnt8),
      lc_count_to_bin(LcCnt9),
      lc_count_to_bin(LcCnt10),
      lc_count_to_bin(LcCnt11),
      lc_count_to_bin(LcCnt12),
      lc_count_to_bin(LcCnt13),
      lc_count_to_bin(LcCnt14),
      lc_count_to_bin(LcCnt15),
      lc_count_to_bin(LcCnt16),
      lc_count_to_bin(LcCnt17),
      lc_count_to_bin(LcCnt18),
      lc_count_to_bin(LcCnt19),
      lc_count_to_bin(LcCnt20),
      lc_count_to_bin(LcCnt21),
      lc_count_to_bin(LcCnt22),
      lc_count_to_bin(LcCnt23),
      lc_count_to_bin(LcCnt24)
  };


  // States with OTP test registers active
  parameter lc_state_e LC_CTRL_OTP_TEST_REG_ENABLED_STATES[17] = '{
      LcStRaw,
      LcStTestUnlocked0,
      LcStTestLocked0,
      LcStTestUnlocked1,
      LcStTestLocked1,
      LcStTestUnlocked2,
      LcStTestLocked2,
      LcStTestUnlocked3,
      LcStTestLocked3,
      LcStTestUnlocked4,
      LcStTestLocked4,
      LcStTestUnlocked5,
      LcStTestLocked5,
      LcStTestUnlocked6,
      LcStTestLocked6,
      LcStTestUnlocked7,
      LcStRma
  };

  // Counts with OTP test registers enabled
  parameter lc_cnt_e LC_CTRL_OTP_TEST_REG_ENABLED_COUNTS[25] = '{
      LcCnt0,
      LcCnt1,
      LcCnt2,
      LcCnt3,
      LcCnt4,
      LcCnt5,
      LcCnt6,
      LcCnt7,
      LcCnt8,
      LcCnt9,
      LcCnt10,
      LcCnt11,
      LcCnt12,
      LcCnt13,
      LcCnt14,
      LcCnt15,
      LcCnt16,
      LcCnt17,
      LcCnt18,
      LcCnt19,
      LcCnt20,
      LcCnt21,
      LcCnt22,
      LcCnt23,
      LcCnt24
  };
endpackage
