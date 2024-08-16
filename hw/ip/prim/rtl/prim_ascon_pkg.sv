// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_ascon_pkg;

parameter int AsconRoundCountW = 4;

// Due to Ascon's round constants the current_round
// contains an offset:
// for P12 we count: from 0 to 11 = 12 rounds,
// for P8  we count: from 4 to 11 =  8 rounds,
// for P6  we count: from 5 to 11 =  6 rounds

typedef enum logic [3:0] {
  P12 = 4'b0000,
  P8  = 4'b0100,
  P6  = 4'b0110
} perm_offset_e;

parameter int DUPLEX_OP_WIDTH = 3;

typedef enum logic [DUPLEX_OP_WIDTH-1:0] {
  ASCON_ENC  = 3'b001,
  ASCON_DEC  = 3'b010,
  ASCON_HASH = 3'b100
} duplex_op_e;

parameter int DUPLEX_VARIANT_WIDTH = 2;

typedef enum logic [DUPLEX_VARIANT_WIDTH-1:0] {
  ASCON_128  = 2'b01,
  ASCON_128A = 2'b10
} duplex_variant_e;

localparam logic [63:0] IV_128  = 64'h80400c0600000000;
localparam logic [63:0] IV_128A = 64'h80800c0800000000;

localparam logic [3:0] ROUND_MAX = 4'b1011;

// Round constants
function automatic logic [7:0] get_ascon_rcon(logic [3:0] round);
  logic [7:0] result;
  unique case (round)
    4'b0000: result = 8'hf0;
    4'b0001: result = 8'he1;
    4'b0010: result = 8'hd2;
    4'b0011: result = 8'hc3;
    4'b0100: result = 8'hb4;
    4'b0101: result = 8'ha5;
    4'b0110: result = 8'h96;
    4'b0111: result = 8'h87;
    4'b1000: result = 8'h78;
    4'b1001: result = 8'h69;
    4'b1010: result = 8'h5a;
    4'b1011: result = 8'h4b;
    default: result = 8'h00;
  endcase

  return result;
endfunction

parameter int KEY_HI_LOW_MUX_WIDTH = 1;
typedef enum logic [KEY_HI_LOW_MUX_WIDTH-1:0] {
  KEY_LOW = 1'b0,
  KEY_HI  = 1'b1
} key_hi_low_mux_e;

parameter int WORD_LOW_KEY_HI_MUX_WIDTH = 1;
typedef enum logic [WORD_LOW_KEY_HI_MUX_WIDTH-1:0] {
  WORD = 1'b0,
  KEY  = 1'b1
} word_low_key_hi_mux_e;

parameter int ASCON_WORD_MUX_WIDTH = 2;
typedef enum logic [ASCON_WORD_MUX_WIDTH-1:0] {
  INIT   = 2'b00,
  ABSORB = 2'b01,
  KEEP   = 2'b10,
  ROUND  = 2'b11
} ascon_word_mux_e;

parameter int ROUND_INPUT_MUX_WIDTH = 1;
typedef enum logic [ROUND_INPUT_MUX_WIDTH-1:0] {
  STATE    = 1'b0,
  BLINDING = 1'b1
} ascon_round_input_mux_e;

parameter int PADDING_MUX_WIDTH = 2;
typedef enum logic [PADDING_MUX_WIDTH-1:0] {
  DATA_IN_PAD  = 2'b00,
  DATA_OUT_PAD = 2'b01,
  EMPTY_PAD    = 2'b10
} padding_mux_e;

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 18 -n 10 \
//     -s 3538518573 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: ||||||||||| (13.73%)
//  4: |||||||||||||||| (20.92%)
//  5: |||||||||||||||||||| (24.84%)
//  6: |||||||||||||||| (20.92%)
//  7: ||||||||||| (14.38%)
//  8: |||| (5.23%)
//  9: --
// 10: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 8
// Minimum Hamming weight: 3
// Maximum Hamming weight: 8
//
localparam int AsconFSMStateWidth = 10;
typedef enum logic [AsconFSMStateWidth-1:0] {
  Idle             = 10'b1010101110,
  Init             = 10'b0110000110,
  PermInit         = 10'b1011110110,
  Xor0Key          = 10'b0001010011,
  AbsorbAD         = 10'b1110010000,
  PermAD           = 10'b1101101101,
  XorDomSep        = 10'b0100110010,
  AbsorbMSG        = 10'b0011100011,
  PermMSG          = 10'b0001001100,
  AbsorbMSGEmpty   = 10'b0100101100,
  XorKey0          = 10'b1000011011,
  PermFinal        = 10'b0011010000,
  SqueezeTagXorKey = 10'b1111010111,
  PermADLast       = 10'b1010000010,
  AbsorbADEmpty    = 10'b1101111011,
  PermMSGEmpty     = 10'b1011111000,
  PermADEmpty      = 10'b0010111100,
  Error            = 10'b0100011110
} fsm_state_e;

function automatic logic [127:0] bin2thermo(logic [4:0] valid_bytes);
  logic [127:0] valid_bytes_mask;
  unique case (valid_bytes)
    5'b00000 : valid_bytes_mask =               {128{1'b0}};
    5'b00001 : valid_bytes_mask = {  {8{1'b1}}, {120{1'b0}}};
    5'b00010 : valid_bytes_mask = { {16{1'b1}}, {112{1'b0}}};
    5'b00011 : valid_bytes_mask = { {24{1'b1}}, {104{1'b0}}};
    5'b00100 : valid_bytes_mask = { {32{1'b1}},  {96{1'b0}}};
    5'b00101 : valid_bytes_mask = { {40{1'b1}},  {88{1'b0}}};
    5'b00110 : valid_bytes_mask = { {48{1'b1}},  {80{1'b0}}};
    5'b00111 : valid_bytes_mask = { {56{1'b1}},  {72{1'b0}}};
    5'b01000 : valid_bytes_mask = { {64{1'b1}},  {64{1'b0}}};
    5'b01001 : valid_bytes_mask = { {72{1'b1}},  {56{1'b0}}};
    5'b01010 : valid_bytes_mask = { {80{1'b1}},  {48{1'b0}}};
    5'b01011 : valid_bytes_mask = { {88{1'b1}},  {40{1'b0}}};
    5'b01100 : valid_bytes_mask = { {96{1'b1}},  {32{1'b0}}};
    5'b01101 : valid_bytes_mask = {{104{1'b1}},  {24{1'b0}}};
    5'b01110 : valid_bytes_mask = {{112{1'b1}},  {16{1'b0}}};
    5'b01111 : valid_bytes_mask = {{120{1'b1}},   {8{1'b0}}};
    default :  valid_bytes_mask =  {128{1'b1}};
  endcase

  return valid_bytes_mask;
endfunction

function automatic logic [127:0] get_padding_mask(logic [4:0] valid_bytes);
  logic [127:0] padding_byte_mask;
  unique case (valid_bytes)
    5'b00000 : padding_byte_mask = {             8'h80, {120{1'b0}}};
    5'b00001 : padding_byte_mask = {  {8{1'b0}}, 8'h80, {112{1'b0}}};
    5'b00010 : padding_byte_mask = { {16{1'b0}}, 8'h80, {104{1'b0}}};
    5'b00011 : padding_byte_mask = { {24{1'b0}}, 8'h80,  {96{1'b0}}};
    5'b00100 : padding_byte_mask = { {32{1'b0}}, 8'h80,  {88{1'b0}}};
    5'b00101 : padding_byte_mask = { {40{1'b0}}, 8'h80,  {80{1'b0}}};
    5'b00110 : padding_byte_mask = { {48{1'b0}}, 8'h80,  {72{1'b0}}};
    5'b00111 : padding_byte_mask = { {56{1'b0}}, 8'h80,  {64{1'b0}}};
    5'b01000 : padding_byte_mask = { {64{1'b0}}, 8'h80,  {56{1'b0}}};
    5'b01001 : padding_byte_mask = { {72{1'b0}}, 8'h80,  {48{1'b0}}};
    5'b01010 : padding_byte_mask = { {80{1'b0}}, 8'h80,  {40{1'b0}}};
    5'b01011 : padding_byte_mask = { {88{1'b0}}, 8'h80,  {32{1'b0}}};
    5'b01100 : padding_byte_mask = { {96{1'b0}}, 8'h80,  {24{1'b0}}};
    5'b01101 : padding_byte_mask = {{104{1'b0}}, 8'h80,  {16{1'b0}}};
    5'b01110 : padding_byte_mask = {{112{1'b0}}, 8'h80,   {8{1'b0}}};
    5'b01111 : padding_byte_mask = {{120{1'b0}}, 8'h80             };
    default :  padding_byte_mask =  {128{1'b0}};
  endcase

  return padding_byte_mask;
endfunction


endpackage : prim_ascon_pkg
