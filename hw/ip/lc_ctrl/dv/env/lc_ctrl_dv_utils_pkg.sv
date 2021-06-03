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
  const dec_lc_state_e VALID_NEXT_STATES [dec_lc_state_e][$] = '{
    DecLcStRma:     {DecLcStScrap},
    DecLcStProdEnd: {DecLcStScrap},
    DecLcStProd:    {DecLcStScrap, DecLcStRma},
    DecLcStDev:     {DecLcStScrap, DecLcStRma},
    DecLcStTestUnlocked3: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev},
    DecLcStTestUnlocked2: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2},
    DecLcStTestUnlocked1: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2, DecLcStTestLocked1},
    DecLcStTestUnlocked0: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2, DecLcStTestLocked1, DecLcStTestLocked0},
    DecLcStTestLocked2: {DecLcStScrap, DecLcStProdEnd, DecLcStProd,
                         DecLcStDev, DecLcStTestUnlocked3},
    DecLcStTestLocked1: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked3, DecLcStTestUnlocked2},
    DecLcStTestLocked0: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked3, DecLcStTestUnlocked2, DecLcStTestUnlocked1},
    DecLcStRaw: {DecLcStScrap, DecLcStTestUnlocked2, DecLcStTestUnlocked1, DecLcStTestUnlocked0}
  };

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
      LcStDev:           return DecLcStDev;
      LcStProd:          return DecLcStProd;
      LcStProdEnd:       return DecLcStProdEnd;
      LcStRma:           return DecLcStRma;
      LcStScrap:         return DecLcStScrap;
      default: `uvm_fatal("lc_env_pkg", $sformatf("unknown lc_state 0x%0h", curr_state))
    endcase
  endfunction

  function automatic lc_state_e encode_lc_state(dec_lc_state_e curr_state);
    case (curr_state)
      DecLcStRaw:           return LcStRaw;
      DecLcStTestUnlocked0: return LcStTestUnlocked0;
      DecLcStTestLocked0:   return LcStTestLocked0;
      DecLcStTestUnlocked1: return LcStTestUnlocked1;
      DecLcStTestLocked1:   return LcStTestLocked1;
      DecLcStTestUnlocked2: return LcStTestUnlocked2;
      DecLcStTestLocked2:   return LcStTestLocked2;
      DecLcStTestUnlocked3: return LcStTestUnlocked3;
      DecLcStDev:           return LcStDev;
      DecLcStProd:          return LcStProd;
      DecLcStProdEnd:       return LcStProdEnd;
      DecLcStRma:           return LcStRma;
      DecLcStScrap:         return LcStScrap;
      default: `uvm_fatal("lc_env_pkg", $sformatf("unknown lc_state 0x%0h", curr_state))
    endcase
  endfunction

  function automatic int dec_lc_cnt(lc_cnt_e curr_cnt);
    case (curr_cnt)
      LcCnt0  : return 0;
      LcCnt1  : return 1;
      LcCnt2  : return 2;
      LcCnt3  : return 3;
      LcCnt4  : return 4;
      LcCnt5  : return 5;
      LcCnt6  : return 6;
      LcCnt7  : return 7;
      LcCnt8  : return 8;
      LcCnt9  : return 9;
      LcCnt10 : return 10;
      LcCnt11 : return 11;
      LcCnt12 : return 12;
      LcCnt13 : return 13;
      LcCnt14 : return 14;
      LcCnt15 : return 15;
      LcCnt16 : return 16;
      default: `uvm_fatal("lc_env_pkg", $sformatf("unknown lc_cnt 0x%0h", curr_cnt))
    endcase
  endfunction

endpackage
