// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_

#include "aes_tlul_sequence_common.h"
#include "crypto.h"

// Example 0 - encrypt/decrypt all key lenghts

static const int num_transactions_max = 1 + 3 * (21 + 8 + 8) + 7 + 4 + 6;
static const TLI tl_i_transactions[num_transactions_max] = {
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    // AES-128
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 128-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 128-bit
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0x16157E2B, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0xA6D2AE28, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0x8815F7AB, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0x3C4FCF09, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0xFFFFFFFF, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0xFFFFFFFF, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0xA8F64332, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x8D305A88, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xA2983131, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0x340737E0, 0, true},

    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 128-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 128-bit
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x1, 0, true},  // start
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    // AES-192
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x2 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 192-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x2 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 192-bit
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0xF7B0738E, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0x52640EDA, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0x2BF310C8, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0xE5799080, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0xD2EAF862, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0x7B6B2C52, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0xFFFFFFFF, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0xFFFFFFFF, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0xFFFFFFFF, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0xA8F64332, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x8D305A88, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xA2983131, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0x340737E0, 0, true},

    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x2 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 192-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x2 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 192-bit
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x1, 0, true},  // start
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    // Produce ctrl update error
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 128-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x2 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 192-bit
    // Try to start with invalid mode
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesNone << 1) | 0x0,
     0, true},  // ctrl - decrypt, 128-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x1 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesNone << 1) | 0x0,
     0, true},  // ctrl - decrypt, 128-bit
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x1, 0, true},  // start
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},   // wait for idle
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x0, 0, true},  // disable start

    // AES-256
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 256-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 256-bit
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0x10EB3D60, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0xBE71CA15, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0xF0AE732B, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0x81777D85, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0x072C351F, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0xD708613B, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0xA310982D, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0xF4DF1409, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0xA8F64332, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x8D305A88, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xA2983131, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0x340737E0, 0, true},

    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 256-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x1 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x0,
     0, true},  // ctrl - encrypt, 256-bit
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x1, 0, true},  // start

    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},  // wait for busy
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0, 0xF, 0x55555555, 0,
     true},  // try to overwrite key0
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF, 0xFFFFFFFF, 0,
     true},  // try to overwrite ctrl
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF, 0xFFFFFFFF, 0,
     true},  // try to overwrite ctrl

    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    // Clear
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x3E, 0, true},  // clear
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
};

static const int num_responses_max = 1 + 18 + 18 + 1 + 1 + 5;
static const EXP_RESP tl_o_exp_resp[num_responses_max] = {
    {0x1, 0x1},  // status shows idle

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

    {0x1, 0x1},  // status shows idle

    {0x4, 0x4},  // status shows output valid
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x0, 0x0},  // don't care
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x1, 0x0},  // status shows busy

    {0x4, 0x4},  // status shows output valid
    {0xFFFFFFFF, 0x3A612130},
    {0xFFFFFFFF, 0x2F583E97},
    {0xFFFFFFFF, 0x4123294A},
    {0xFFFFFFFF, 0x94C4AE37},
    {0x4, 0x0},  // status shows output valid no longer valid

    {0x1, 0x1},  // status shows idle
    {0x0, 0x0},  // data_out0 cleared to random value
    {0x0, 0x0},  // data_out1 cleared to random value
    {0x0, 0x0},  // data_out2 cleared to random value
    {0x0, 0x0},  // data_out3 cleared to random value
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_0_H_
