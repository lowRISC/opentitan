// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_

// Example 0 - Encode/Decode all key lenghts

static const int num_transactions_max = 57 + 24 + 6 + 2;
static const TLI tl_i_transactions[num_transactions_max] = {
    // AES-128
    {true, 0, 0, 2, 0, 0x40, 0xF, 0x3, 0, true},  // ctrl - decode, 128-bit
    {true, 0, 0, 2, 0, 0x00, 0xF, 0x16157E2B, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0xA6D2AE28, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0x8815F7AB, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0x3C4FCF09, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0xFFFFFFFF, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0xFFFFFFFF, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0xFFFFFFFF, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0xFFFFFFFF, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0xA8F64332, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x8D305A88, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xA2983131, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0x340737E0, 0, true},  // data_in3

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
    {true, 0, 0, 2, 0, 0x00, 0xF, 0xF7B0738E, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0x52640EDA, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0x2BF310C8, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0xE5799080, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0xD2EAF862, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0x7B6B2C52, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0xFFFFFFFF, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0xFFFFFFFF, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0xA8F64332, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x8D305A88, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xA2983131, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0x340737E0, 0, true},  // data_in3

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
    {true, 0, 0, 2, 0, 0x00, 0xF, 0x10EB3D60, 0, true},  // key0
    {true, 0, 0, 2, 0, 0x04, 0xF, 0xBE71CA15, 0, true},  // key1
    {true, 0, 0, 2, 0, 0x08, 0xF, 0xF0AE732B, 0, true},  // key2
    {true, 0, 0, 2, 0, 0x0C, 0xF, 0x81777D85, 0, true},  // key3
    {true, 0, 0, 2, 0, 0x10, 0xF, 0x072C351F, 0, true},  // key4
    {true, 0, 0, 2, 0, 0x14, 0xF, 0xD708613B, 0, true},  // key5
    {true, 0, 0, 2, 0, 0x18, 0xF, 0xA310982D, 0, true},  // key6
    {true, 0, 0, 2, 0, 0x1c, 0xF, 0xF4DF1409, 0, true},  // key7

    {true, 0, 0, 2, 0, 0x20, 0xF, 0xA8F64332, 0, true},  // data_in0
    {true, 0, 0, 2, 0, 0x24, 0xF, 0x8D305A88, 0, true},  // data_in1
    {true, 0, 0, 2, 0, 0x28, 0xF, 0xA2983131, 0, true},  // data_in2
    {true, 0, 0, 2, 0, 0x2C, 0xF, 0x340737E0, 0, true},  // data_in3

    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status

    {true, 0, 0, 2, 0, 0x40, 0xF, 0x18, 0, true},  // ctrl - encode, 256-bit
    {true, 0, 0, 2, 0, 0x44, 0xF, 0x1, 0, true},   // trigger

    {true, 0, 0, 2, 0, 0x00, 0xF, 0x55555555, 0,
     true},  // try to overwrite key0
    {true, 0, 0, 2, 0, 0x40, 0xF, 0xFFFFFFFF, 0,
     true},  // try to overwrite ctrl

    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status
    {true, 4, 0, 2, 0, 0x30, 0xF, 0x0, 0, true},  // read data_out0
    {true, 4, 0, 2, 0, 0x34, 0xF, 0x0, 0, true},  // read data_out1
    {true, 4, 0, 2, 0, 0x38, 0xF, 0x0, 0, true},  // read data_out2
    {true, 4, 0, 2, 0, 0x3C, 0xF, 0x0, 0, true},  // read data_out3
    {true, 4, 0, 2, 0, 0x48, 0xF, 0x0, 0, true},  // read status

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
    {0xFFFFFFFF, 0x1D842539},
    {0xFFFFFFFF, 0xFB09DC02},
    {0xFFFFFFFF, 0x978511DC},
    {0xFFFFFFFF, 0x320B6A19},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0xB69F5E58},
    {0xFFFFFFFF, 0x9A2B72C2},
    {0xFFFFFFFF, 0xC192F4F4},
    {0xFFFFFFFF, 0xC124B02B},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0x3A612130},
    {0xFFFFFFFF, 0x2F583E97},
    {0xFFFFFFFF, 0x4123294A},
    {0xFFFFFFFF, 0x94C4AE37},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0xE, 0x0},         // trigger cleared
    {0xFFFFFFFF, 0x0},  // data_out0 cleared
    {0xFFFFFFFF, 0x0},  // data_out1 cleared
    {0xFFFFFFFF, 0x0},  // data_out2 cleared
    {0xFFFFFFFF, 0x0},  // data_out3 cleared
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_
