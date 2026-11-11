// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle state encoding definition.
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED

package lc_ctrl_state_pkg;

  import prim_util_pkg::vbits;

  ///////////////////////////////
  // General size declarations //
  ///////////////////////////////

  parameter int LcValueWidth = 16;

  parameter int NumLcStateValues = 20;
  parameter int LcStateWidth = NumLcStateValues * LcValueWidth;
  parameter int NumLcStates = 21;
  parameter int DecLcStateWidth = vbits(NumLcStates);
  parameter int NumSocDbgStateValues = 2;
  parameter int SocDbgStateWidth = NumSocDbgStateValues * LcValueWidth;
  parameter int NumOwnershipStateValues = 8;
  parameter int OwnershipStateWidth = NumOwnershipStateValues * LcValueWidth;
  parameter int NumAuthStateValues = 2;
  parameter int AuthStateWidth = NumAuthStateValues * LcValueWidth;

  // Redundant version used in the CSRs.
  parameter int DecLcStateNumRep = 32/DecLcStateWidth;
  parameter int ExtDecLcStateWidth = DecLcStateNumRep*DecLcStateWidth;

  parameter int NumLcCountValues = 24;
  parameter int LcCountWidth = NumLcCountValues * LcValueWidth;
  parameter int NumLcCountStates = 25;
  parameter int DecLcCountWidth = vbits(NumLcCountStates);

  // This state is not stored in OTP, but inferred from the locked
  // status of the secret partitions. Hence, only the decoded ID state
  // is declared here for exposure through the CSR interface.
  parameter int NumLcIdStates = 2;
  parameter int DecLcIdStateWidth = vbits(NumLcIdStates+1);
  // Redundant version used in the CSRs.
  parameter int DecLcIdStateNumRep = 32/DecLcIdStateWidth;
  parameter int ExtDecLcIdStateWidth = DecLcIdStateNumRep*DecLcIdStateWidth;

  /////////////////////////////////////////////
  // Life cycle manufacturing state encoding //
  /////////////////////////////////////////////

  // These values have been generated such that they are incrementally writeable with respect
  // to the ECC polynomial specified. The values are used to define the life cycle manufacturing
  // state and transition counter encoding in lc_ctrl_pkg.sv.
  //
  // The values are unique and have the following statistics (considering all 16
  // data and 6 ECC bits):
  //
  // - Minimum Hamming weight: 4
  // - Maximum Hamming weight: 16
  // - Minimum Hamming distance from any other value: 4
  // - Maximum Hamming distance from any other value: 20
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4:  (1.35%)
  //  5: --
  //  6: |||| (5.93%)
  //  7: --
  //  8: ||||||||||||| (18.42%)
  //  9: --
  // 10: ||||||||||||||||||| (27.40%)
  // 11: --
  // 12: |||||||||||||||||||| (27.68%)
  // 13: --
  // 14: |||||||||| (14.57%)
  // 15: --
  // 16: || (4.13%)
  // 17: --
  // 18:  (0.50%)
  // 19: --
  // 20:  (0.02%)
  // 21: --
  // 22: --
  //
  //
  // Note that the ECC bits are not defined in this package as they will be calculated by
  // the OTP ECC logic at runtime.

  // The A/B/K/L values are used for the encoded LC state. In each word, the
  // values 0 -> A -> B -> K -> L -> ONE only ever set bits (data and ECC).
  parameter logic [15:0] A0 = 16'b0000001010100000; // ECC: 6'b001000
  parameter logic [15:0] B0 = 16'b1000001010100101; // ECC: 6'b011000
  parameter logic [15:0] K0 = 16'b1000011110101111; // ECC: 6'b011000
  parameter logic [15:0] L0 = 16'b1010111111111111; // ECC: 6'b011000

  parameter logic [15:0] A1 = 16'b1111000000000000; // ECC: 6'b000000
  parameter logic [15:0] B1 = 16'b1111100110000000; // ECC: 6'b010000
  parameter logic [15:0] K1 = 16'b1111111110001100; // ECC: 6'b010000
  parameter logic [15:0] L1 = 16'b1111111111101110; // ECC: 6'b010100

  parameter logic [15:0] A2 = 16'b0000001100001000; // ECC: 6'b000100
  parameter logic [15:0] B2 = 16'b0000011111001000; // ECC: 6'b001100
  parameter logic [15:0] K2 = 16'b0110011111001010; // ECC: 6'b001110
  parameter logic [15:0] L2 = 16'b1110011111001111; // ECC: 6'b011110

  parameter logic [15:0] A3 = 16'b0000001011010000; // ECC: 6'b000000
  parameter logic [15:0] B3 = 16'b1010001011010000; // ECC: 6'b000110
  parameter logic [15:0] K3 = 16'b1010001111010101; // ECC: 6'b001110
  parameter logic [15:0] L3 = 16'b1110111111110101; // ECC: 6'b001110

  parameter logic [15:0] A4 = 16'b0000000110001100; // ECC: 6'b000000
  parameter logic [15:0] B4 = 16'b0000010110001101; // ECC: 6'b001100
  parameter logic [15:0] K4 = 16'b0000011110011111; // ECC: 6'b001110
  parameter logic [15:0] L4 = 16'b0011011111111111; // ECC: 6'b001110

  parameter logic [15:0] A5 = 16'b0000001101000000; // ECC: 6'b001000
  parameter logic [15:0] B5 = 16'b0000011111000110; // ECC: 6'b001000
  parameter logic [15:0] K5 = 16'b1000111111001111; // ECC: 6'b001000
  parameter logic [15:0] L5 = 16'b1101111111001111; // ECC: 6'b001110

  parameter logic [15:0] A6 = 16'b0000000001011010; // ECC: 6'b000000
  parameter logic [15:0] B6 = 16'b1001010001011010; // ECC: 6'b001000
  parameter logic [15:0] K6 = 16'b1001011011011110; // ECC: 6'b001100
  parameter logic [15:0] L6 = 16'b1111011111111110; // ECC: 6'b001100

  parameter logic [15:0] A7 = 16'b0000000110010000; // ECC: 6'b001000
  parameter logic [15:0] B7 = 16'b0101000110010000; // ECC: 6'b001110
  parameter logic [15:0] K7 = 16'b1101110111010000; // ECC: 6'b001110
  parameter logic [15:0] L7 = 16'b1111110111010110; // ECC: 6'b011110

  parameter logic [15:0] A8 = 16'b1000000100000000; // ECC: 6'b011000
  parameter logic [15:0] B8 = 16'b1000000101100001; // ECC: 6'b011010
  parameter logic [15:0] K8 = 16'b1001100101100111; // ECC: 6'b011010
  parameter logic [15:0] L8 = 16'b1001110111101111; // ECC: 6'b011110

  parameter logic [15:0] A9 = 16'b0101000000000011; // ECC: 6'b000000
  parameter logic [15:0] B9 = 16'b0111100001010011; // ECC: 6'b000000
  parameter logic [15:0] K9 = 16'b0111101001110111; // ECC: 6'b000010
  parameter logic [15:0] L9 = 16'b0111111011111111; // ECC: 6'b000110

  parameter logic [15:0] A10 = 16'b0000000001100001; // ECC: 6'b000010
  parameter logic [15:0] B10 = 16'b0000001101100111; // ECC: 6'b000010
  parameter logic [15:0] K10 = 16'b1100101101100111; // ECC: 6'b010010
  parameter logic [15:0] L10 = 16'b1100111111101111; // ECC: 6'b010110

  parameter logic [15:0] A11 = 16'b0000010101010000; // ECC: 6'b000000
  parameter logic [15:0] B11 = 16'b0001010101010100; // ECC: 6'b010100
  parameter logic [15:0] K11 = 16'b0001010111110111; // ECC: 6'b010100
  parameter logic [15:0] L11 = 16'b1011011111110111; // ECC: 6'b011100

  parameter logic [15:0] A12 = 16'b0000010010000110; // ECC: 6'b000000
  parameter logic [15:0] B12 = 16'b0000010011100111; // ECC: 6'b000010
  parameter logic [15:0] K12 = 16'b1000010111100111; // ECC: 6'b011010
  parameter logic [15:0] L12 = 16'b1110011111110111; // ECC: 6'b011010

  parameter logic [15:0] A13 = 16'b0000000100011001; // ECC: 6'b000000
  parameter logic [15:0] B13 = 16'b0010000100011111; // ECC: 6'b010000
  parameter logic [15:0] K13 = 16'b1011010100011111; // ECC: 6'b011000
  parameter logic [15:0] L13 = 16'b1111111101011111; // ECC: 6'b011000

  parameter logic [15:0] A14 = 16'b0000000000011100; // ECC: 6'b001000
  parameter logic [15:0] B14 = 16'b1000110001011100; // ECC: 6'b001000
  parameter logic [15:0] K14 = 16'b1000110011111111; // ECC: 6'b001000
  parameter logic [15:0] L14 = 16'b1101110011111111; // ECC: 6'b001110

  parameter logic [15:0] A15 = 16'b0000001000010010; // ECC: 6'b000010
  parameter logic [15:0] B15 = 16'b0100101100010010; // ECC: 6'b001010
  parameter logic [15:0] K15 = 16'b0100111101011011; // ECC: 6'b001010
  parameter logic [15:0] L15 = 16'b0101111101011111; // ECC: 6'b011110

  parameter logic [15:0] A16 = 16'b1100011000000000; // ECC: 6'b000000
  parameter logic [15:0] B16 = 16'b1100011100011001; // ECC: 6'b000000
  parameter logic [15:0] K16 = 16'b1101111100011111; // ECC: 6'b000000
  parameter logic [15:0] L16 = 16'b1101111110111111; // ECC: 6'b000110

  parameter logic [15:0] A17 = 16'b1010000101000000; // ECC: 6'b000000
  parameter logic [15:0] B17 = 16'b1011100101001000; // ECC: 6'b000100
  parameter logic [15:0] K17 = 16'b1011110101101101; // ECC: 6'b000100
  parameter logic [15:0] L17 = 16'b1111110111101101; // ECC: 6'b011100

  parameter logic [15:0] A18 = 16'b1100000000000010; // ECC: 6'b000100
  parameter logic [15:0] B18 = 16'b1111000110000010; // ECC: 6'b000100
  parameter logic [15:0] K18 = 16'b1111100111100010; // ECC: 6'b010100
  parameter logic [15:0] L18 = 16'b1111100111110011; // ECC: 6'b011110

  parameter logic [15:0] A19 = 16'b0000010000000001; // ECC: 6'b001100
  parameter logic [15:0] B19 = 16'b1000110100010001; // ECC: 6'b001100
  parameter logic [15:0] K19 = 16'b1010110100010111; // ECC: 6'b011100
  parameter logic [15:0] L19 = 16'b1111110110110111; // ECC: 6'b011100


  // The C/D values are used for the encoded LC transition counter.
  parameter logic [15:0] C0 = 16'b0100100101100000; // ECC: 6'b101001
  parameter logic [15:0] D0 = 16'b1110110101110011; // ECC: 6'b101111

  parameter logic [15:0] C1 = 16'b1110101000110011; // ECC: 6'b001000
  parameter logic [15:0] D1 = 16'b1110111100111111; // ECC: 6'b001011

  parameter logic [15:0] C2 = 16'b0011110000011101; // ECC: 6'b010100
  parameter logic [15:0] D2 = 16'b0011110111011101; // ECC: 6'b111110

  parameter logic [15:0] C3 = 16'b0000110110100101; // ECC: 6'b010000
  parameter logic [15:0] D3 = 16'b0011110110101111; // ECC: 6'b010011

  parameter logic [15:0] C4 = 16'b1011000010101001; // ECC: 6'b010110
  parameter logic [15:0] D4 = 16'b1111111010101011; // ECC: 6'b010111

  parameter logic [15:0] C5 = 16'b1110010000111000; // ECC: 6'b011001
  parameter logic [15:0] D5 = 16'b1111110101111010; // ECC: 6'b111001

  parameter logic [15:0] C6 = 16'b0000010011000001; // ECC: 6'b101011
  parameter logic [15:0] D6 = 16'b1001010111011001; // ECC: 6'b101111

  parameter logic [15:0] C7 = 16'b1100101110100010; // ECC: 6'b110000
  parameter logic [15:0] D7 = 16'b1100101111101111; // ECC: 6'b111001

  parameter logic [15:0] C8 = 16'b0010100101000101; // ECC: 6'b100001
  parameter logic [15:0] D8 = 16'b0111100101101111; // ECC: 6'b101111

  parameter logic [15:0] C9 = 16'b0011000011101010; // ECC: 6'b001110
  parameter logic [15:0] D9 = 16'b0111010111101110; // ECC: 6'b111110

  parameter logic [15:0] C10 = 16'b0111101110110000; // ECC: 6'b001000
  parameter logic [15:0] D10 = 16'b0111111111110101; // ECC: 6'b101001

  parameter logic [15:0] C11 = 16'b0001000111011000; // ECC: 6'b110110
  parameter logic [15:0] D11 = 16'b1101010111111010; // ECC: 6'b110111

  parameter logic [15:0] C12 = 16'b0011110001000000; // ECC: 6'b110100
  parameter logic [15:0] D12 = 16'b1111111101000111; // ECC: 6'b110110

  parameter logic [15:0] C13 = 16'b1111000001011101; // ECC: 6'b100000
  parameter logic [15:0] D13 = 16'b1111101011011101; // ECC: 6'b110011

  parameter logic [15:0] C14 = 16'b0010101001101000; // ECC: 6'b001010
  parameter logic [15:0] D14 = 16'b1011111111111000; // ECC: 6'b001010

  parameter logic [15:0] C15 = 16'b1101011100010100; // ECC: 6'b110000
  parameter logic [15:0] D15 = 16'b1101011111111100; // ECC: 6'b111010

  parameter logic [15:0] C16 = 16'b0101011000100010; // ECC: 6'b101000
  parameter logic [15:0] D16 = 16'b0101011001111011; // ECC: 6'b101110

  parameter logic [15:0] C17 = 16'b1010010100000110; // ECC: 6'b100111
  parameter logic [15:0] D17 = 16'b1010111111000110; // ECC: 6'b111111

  parameter logic [15:0] C18 = 16'b0001001100011011; // ECC: 6'b011001
  parameter logic [15:0] D18 = 16'b1101001111011011; // ECC: 6'b011111

  parameter logic [15:0] C19 = 16'b1100000110001001; // ECC: 6'b100100
  parameter logic [15:0] D19 = 16'b1111000110101111; // ECC: 6'b101100

  parameter logic [15:0] C20 = 16'b0110100010000011; // ECC: 6'b111100
  parameter logic [15:0] D20 = 16'b0110101011111011; // ECC: 6'b111101

  parameter logic [15:0] C21 = 16'b0000110011010100; // ECC: 6'b110110
  parameter logic [15:0] D21 = 16'b0101110011110110; // ECC: 6'b111111

  parameter logic [15:0] C22 = 16'b1001101010100000; // ECC: 6'b011110
  parameter logic [15:0] D22 = 16'b1001111011100101; // ECC: 6'b111111

  parameter logic [15:0] C23 = 16'b0011100000110100; // ECC: 6'b110101
  parameter logic [15:0] D23 = 16'b0011111010111100; // ECC: 6'b111111


  // The F/E values are used for the encoded SOC_DBG state.
  parameter logic [15:0] E0 = 16'b1100100000110001; // ECC: 6'b110000
  parameter logic [15:0] F0 = 16'b1111100101111101; // ECC: 6'b110110

  parameter logic [15:0] E1 = 16'b0100110001000100; // ECC: 6'b000111
  parameter logic [15:0] F1 = 16'b0110111001011101; // ECC: 6'b010111


  // The G/H values are used for the encoded OWNERSHIP state.
  parameter logic [15:0] G0 = 16'b0001001111101001; // ECC: 6'b011000
  parameter logic [15:0] H0 = 16'b0111001111101001; // ECC: 6'b111111

  parameter logic [15:0] G1 = 16'b1001110100000011; // ECC: 6'b110010
  parameter logic [15:0] H1 = 16'b1111110110001011; // ECC: 6'b111110

  parameter logic [15:0] G2 = 16'b0001101000010111; // ECC: 6'b000100
  parameter logic [15:0] H2 = 16'b0111111100111111; // ECC: 6'b101100

  parameter logic [15:0] G3 = 16'b0101000111100101; // ECC: 6'b000011
  parameter logic [15:0] H3 = 16'b1101100111110111; // ECC: 6'b101011

  parameter logic [15:0] G4 = 16'b1110100100101010; // ECC: 6'b000110
  parameter logic [15:0] H4 = 16'b1110100111111110; // ECC: 6'b101110

  parameter logic [15:0] G5 = 16'b1110010110100100; // ECC: 6'b110000
  parameter logic [15:0] H5 = 16'b1111111110110110; // ECC: 6'b110001

  parameter logic [15:0] G6 = 16'b0111101000101001; // ECC: 6'b100100
  parameter logic [15:0] H6 = 16'b1111111001111001; // ECC: 6'b111100

  parameter logic [15:0] G7 = 16'b1100000011100011; // ECC: 6'b101010
  parameter logic [15:0] H7 = 16'b1110111011101011; // ECC: 6'b101110


  // The I/J values are used for the encoded AUTH state.
  parameter logic [15:0] I0 = 16'b1000011011000100; // ECC: 6'b110101
  parameter logic [15:0] J0 = 16'b1100111011011101; // ECC: 6'b111101

  parameter logic [15:0] I1 = 16'b1110000000110110; // ECC: 6'b110010
  parameter logic [15:0] J1 = 16'b1110011011111110; // ECC: 6'b110011


  parameter logic [15:0] ZRO = 16'h0;
  parameter logic [15:0] ONE = 16'hffff;

  ////////////////////////
  // Derived enum types //
  ////////////////////////

  // Use lc_state_t and lc_cnt_t in interfaces as very wide enumerations ( > 64 bits )
  // are not supported for virtual interfaces by Xcelium yet
  // https://github.com/lowRISC/opentitan/issues/8884 (Cadence issue: cds_46570160)
  // The enumeration types lc_state_e and lc_cnt_e are still ok in other circumstances

  typedef logic [LcStateWidth-1:0] lc_state_t;
  typedef enum lc_state_t {
    LcStRaw           = {ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO},
    LcStTestUnlocked0 = {B19, A18, A17, A16, A15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  A2,  A1,  A0},
    LcStTestLocked0   = {K19, A18, A17, A16, B15, A14, A13, A12, A11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  A2,  A1,  A0},
    LcStTestUnlocked1 = {K19, A18, A17, A16, K15, A14, A13, A12, B11, A10,  A9,  A8,  A7,  A6,  A5,  A4,  A3,  A2,  A1,  A0},
    LcStTestLocked1   = {K19, A18, A17, A16, K15, A14, A13, A12, K11, A10,  A9,  A8,  B7,  A6,  A5,  A4,  A3,  A2,  A1,  A0},
    LcStTestUnlocked2 = {K19, A18, A17, A16, K15, A14, A13, A12, K11, A10,  A9,  A8,  K7,  A6,  A5,  A4,  B3,  A2,  A1,  A0},
    LcStTestLocked2   = {K19, B18, A17, A16, K15, A14, A13, A12, K11, A10,  A9,  A8,  K7,  A6,  A5,  A4,  K3,  A2,  A1,  A0},
    LcStTestUnlocked3 = {K19, K18, A17, A16, K15, B14, A13, A12, K11, A10,  A9,  A8,  K7,  A6,  A5,  A4,  K3,  A2,  A1,  A0},
    LcStTestLocked3   = {K19, K18, A17, A16, K15, K14, A13, A12, K11, B10,  A9,  A8,  K7,  A6,  A5,  A4,  K3,  A2,  A1,  A0},
    LcStTestUnlocked4 = {K19, K18, A17, A16, K15, K14, A13, A12, K11, K10,  A9,  A8,  K7,  B6,  A5,  A4,  K3,  A2,  A1,  A0},
    LcStTestLocked4   = {K19, K18, A17, A16, K15, K14, A13, A12, K11, K10,  A9,  A8,  K7,  K6,  A5,  A4,  K3,  B2,  A1,  A0},
    LcStTestUnlocked5 = {K19, K18, B17, A16, K15, K14, A13, A12, K11, K10,  A9,  A8,  K7,  K6,  A5,  A4,  K3,  K2,  A1,  A0},
    LcStTestLocked5   = {K19, K18, K17, A16, K15, K14, B13, A12, K11, K10,  A9,  A8,  K7,  K6,  A5,  A4,  K3,  K2,  A1,  A0},
    LcStTestUnlocked6 = {K19, K18, K17, A16, K15, K14, K13, A12, K11, K10,  B9,  A8,  K7,  K6,  A5,  A4,  K3,  K2,  A1,  A0},
    LcStTestLocked6   = {K19, K18, K17, A16, K15, K14, K13, A12, K11, K10,  K9,  A8,  K7,  K6,  B5,  A4,  K3,  K2,  A1,  A0},
    LcStTestUnlocked7 = {K19, K18, K17, A16, K15, K14, K13, A12, K11, K10,  K9,  A8,  K7,  K6,  K5,  A4,  K3,  K2,  B1,  A0},
    LcStDev           = {K19, K18, K17, B16, K15, K14, K13, A12, K11, K10,  K9,  K8,  K7,  K6,  K5,  B4,  K3,  K2,  K1,  B0},
    LcStProd          = {K19, K18, K17, B16, K15, K14, K13, B12, K11, K10,  K9,  B8,  K7,  K6,  K5,  A4,  K3,  K2,  K1,  B0},
    LcStProdEnd       = {K19, K18, K17, L16, K15, K14, K13, L12, K11, K10,  K9,  B8,  K7,  K6,  K5,  A4,  K3,  K2,  K1,  A0},
    LcStRma           = {L19, L18, L17, K16, L15, L14, L13, K12, L11, L10,  L9,  L8,  L7,  L6,  L5,  L4,  L3,  L2,  L1,  L0},
    LcStScrap         = {ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE, ONE}
  } lc_state_e;

  typedef logic [LcCountWidth-1:0] lc_cnt_t;
  typedef enum lc_cnt_t {
    LcCnt0  = {ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO},
    LcCnt1  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  C2,  C1,  D0},
    LcCnt2  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  C2,  D1,  D0},
    LcCnt3  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  C3,  D2,  D1,  D0},
    LcCnt4  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  C4,  D3,  D2,  D1,  D0},
    LcCnt5  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  C5,  D4,  D3,  D2,  D1,  D0},
    LcCnt6  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  C6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt7  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  C7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt8  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  C8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt9  = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  C9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt10 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, C10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt11 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, C11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt12 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, C12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt13 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, C13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt14 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, C14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt15 = {C23, C22, C21, C20, C19, C18, C17, C16, C15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt16 = {C23, C22, C21, C20, C19, C18, C17, C16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt17 = {C23, C22, C21, C20, C19, C18, C17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt18 = {C23, C22, C21, C20, C19, C18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt19 = {C23, C22, C21, C20, C19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt20 = {C23, C22, C21, C20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt21 = {C23, C22, C21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt22 = {C23, C22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt23 = {C23, D22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0},
    LcCnt24 = {D23, D22, D21, D20, D19, D18, D17, D16, D15, D14, D13, D12, D11, D10,  D9,  D8,  D7,  D6,  D5,  D4,  D3,  D2,  D1,  D0}
  } lc_cnt_e;

  typedef logic [SocDbgStateWidth-1:0] soc_dbg_state_t;
  parameter soc_dbg_state_t SOC_DBG_STATE_DEFAULT = '0;
  typedef enum soc_dbg_state_t {
    SocDbgStBlank   = {ZRO, ZRO},
    SocDbgStPreProd = { E1,  E0},
    SocDbgStProd    = { F1,  F0}
  } soc_dbg_state_e;

  typedef logic [OwnershipStateWidth-1:0] ownership_state_t;
  typedef enum ownership_state_t {
    OwnershipStBlank     = {ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO, ZRO},
    OwnershipStLocked0   = { G7,  G6,  G5,  G4,  G3,  G2,  G1,  G0},
    OwnershipStReleased0 = { G7,  G6,  G5,  G4,  G3,  G2,  G1,  H0},
    OwnershipStLocked1   = { G7,  G6,  G5,  G4,  G3,  G2,  H1,  H0},
    OwnershipStReleased1 = { G7,  G6,  G5,  G4,  G3,  H2,  H1,  H0},
    OwnershipStLocked2   = { G7,  G6,  G5,  G4,  H3,  H2,  H1,  H0},
    OwnershipStReleased2 = { G7,  G6,  G5,  H4,  H3,  H2,  H1,  H0},
    OwnershipStLocked3   = { G7,  G6,  H5,  H4,  H3,  H2,  H1,  H0},
    OwnershipStScrapped  = { H7,  H6,  H5,  H4,  H3,  H2,  H1,  H0}
  } ownership_state_e;

  typedef logic [AuthStateWidth-1:0] auth_state_t;
  typedef enum auth_state_t {
    AuthStBlank    = {ZRO, ZRO},
    AuthStEnabled  = { I1,  I0},
    AuthStDisabled = { J1,  J0}
  } auth_state_e;

  // Decoded life cycle state, used to interface with CSRs and TAP.
  typedef enum logic [DecLcStateWidth-1:0] {
    DecLcStRaw = 0,
    DecLcStTestUnlocked0 = 1,
    DecLcStTestLocked0 = 2,
    DecLcStTestUnlocked1 = 3,
    DecLcStTestLocked1 = 4,
    DecLcStTestUnlocked2 = 5,
    DecLcStTestLocked2 = 6,
    DecLcStTestUnlocked3 = 7,
    DecLcStTestLocked3 = 8,
    DecLcStTestUnlocked4 = 9,
    DecLcStTestLocked4 = 10,
    DecLcStTestUnlocked5 = 11,
    DecLcStTestLocked5 = 12,
    DecLcStTestUnlocked6 = 13,
    DecLcStTestLocked6 = 14,
    DecLcStTestUnlocked7 = 15,
    DecLcStDev = 16,
    DecLcStProd = 17,
    DecLcStProdEnd = 18,
    DecLcStRma = 19,
    DecLcStScrap = 20,
    DecLcStPostTrans = 21,
    DecLcStEscalate = 22,
    DecLcStInvalid = 23
  } dec_lc_state_e;

  typedef dec_lc_state_e [DecLcStateNumRep-1:0] ext_dec_lc_state_t;

  typedef enum logic [DecLcIdStateWidth-1:0] {
    DecLcIdBlank,
    DecLcIdPersonalized,
    DecLcIdInvalid
  } dec_lc_id_state_e;

  typedef logic [DecLcCountWidth-1:0] dec_lc_cnt_t;

  parameter int LcTokenWidth = 128;
  typedef logic [LcTokenWidth-1:0] lc_token_t;

endpackage : lc_ctrl_state_pkg
