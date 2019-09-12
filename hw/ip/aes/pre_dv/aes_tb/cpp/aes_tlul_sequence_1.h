// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_

// Example 1 - Encode/Decode all key lenghts

static const int num_transactions_max = 57 + 24 + 6;
static const TLI tl_i_transactions[num_transactions_max] = {
    // AES-128
    {true, 0, 0, 2, 0, 0x40, 0xF, 0x3, 0, true},  // ctrl - decode, 128-bit
    {true, 0, 0, 2, 0, 0x00, 0xF, 0x03020100, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0x07060504, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0x0B0A0908, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0x0F0E0D0C, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0x13121110, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0x17161514, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0x1B1A1918, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0x1F1E1D1C, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0x33221100, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x77665544, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xBBAA9988, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0xFFEEDDCC, 0, true},  // data_in3

    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status

    {true, 0, 0, 2, 0, 0x40, 0xF, 0x12, 0, true},  // ctrl - encode, 128-bit
    {true, 0, 0, 2, 0, 0x44, 0xF, 0x1, 0, true},   // trigger
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},   // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},   // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},   // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},   // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status

    // AES-192
    {true, 0, 0, 2, 0, 0x40, 0xF, 0x5, 0, true},  // ctrl - decode, 192-bit
    {true, 0, 0, 2, 0, 0x00, 0xF, 0x03020100, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0x07060504, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0x0B0A0908, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0x0F0E0D0C, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0x13121110, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0x17161514, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0x1B1A1918, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0x1F1E1D1C, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0x33221100, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x77665544, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xBBAA9988, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0xFFEEDDCC, 0, true},  // data_in3

    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status

    {true, 0, 0, 2, 0, 0x40, 0xF, 0x14, 0, true},  // ctrl - encode, 192-bit
    {true, 0, 0, 2, 0, 0x44, 0xF, 0x1, 0, true},   // trigger
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},   // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},   // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},   // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},   // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status

    // AES-256
    {true, 0, 0, 2, 0, 0x40, 0xF, 0x9, 0, true},  // ctrl - decode, 256-bit
    {true, 0, 0, 2, 0, 0x00, 0xF, 0x03020100, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0x07060504, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0x0B0A0908, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0x0F0E0D0C, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0x13121110, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0x17161514, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0x1B1A1918, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0x1F1E1D1C, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0x33221100, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x77665544, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xBBAA9988, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0xFFEEDDCC, 0, true},  // data_in3

    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status

    {true, 0, 0, 2, 0, 0x40, 0xF, 0x18, 0, true},  // ctrl - encode, 256-bit
    {true, 0, 0, 2, 0, 0x44, 0xF, 0x1, 0, true},   // trigger
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},   // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},   // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},   // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},   // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},   // read status

    // Clear
    {true, 0, 0, 2, 0, 0x44, 0xF, 0xE, 0, true},  // trigger - clear

    {true, 4, 0, 2, 0, 0x44, 0xF, 0x0, 0, true},  // read trigger
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
};

static const int num_responses_max = 18 + 18 + 5;
static const EXP_RESP tl_o_exp_resp[num_responses_max] = {
    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0xD8E0C469},
    {0xFFFFFFFF, 0x30047B6A},
    {0xFFFFFFFF, 0x80B7CDD8},
    {0xFFFFFFFF, 0x5AC5B470},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0xA47CA9DD},
    {0xFFFFFFFF, 0xE0DF4C86},
    {0xFFFFFFFF, 0xA070AF6E},
    {0xFFFFFFFF, 0x91710DEC},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0xCAB7A28E},
    {0xFFFFFFFF, 0xBF456751},
    {0xFFFFFFFF, 0x9049FCEA},
    {0xFFFFFFFF, 0x8960494B},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0xE, 0x0},         // trigger cleared
    {0xFFFFFFFF, 0x0},  // data_out0 cleared
    {0xFFFFFFFF, 0x0},  // data_out1 cleared
    {0xFFFFFFFF, 0x0},  // data_out2 cleared
    {0xFFFFFFFF, 0x0},  // data_out3 cleared
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_
