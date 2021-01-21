// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_

#include "aes_tlul_sequence_common.h"
#include "crypto.h"

// Example 1 - encrypt/decrypt all key lenghts

static const int num_transactions_max = 1 + 3 * (21 + 8 + 8) + 6;
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
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0x03020100, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0x07060504, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0x0B0A0908, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0x0F0E0D0C, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0x13121110, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0x17161514, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0x1B1A1918, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0x1F1E1D1C, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0x33221100, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x77665544, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xBBAA9988, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0xFFEEDDCC, 0, true},

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
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0x03020100, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0x07060504, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0x0B0A0908, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0x0F0E0D0C, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0x13121110, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0x17161514, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0x1B1A1918, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0x1F1E1D1C, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0x33221100, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x77665544, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xBBAA9988, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0xFFEEDDCC, 0, true},

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

    // AES-256
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 256-bit
    {true, 0, 0, 2, 0, AES_CONFIG, 0xF,
     (0x0 << AES_CTRL_MANUAL_OPERATION_OFFSET) |
         (0x4 << AES_CTRL_KEY_LEN_OFFSET) | (kCryptoAesEcb << 1) | 0x1,
     0, true},  // ctrl - decrypt, 256-bit
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x00, 0xF, 0x03020100, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x04, 0xF, 0x07060504, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x08, 0xF, 0x0B0A0908, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x0C, 0xF, 0x0F0E0D0C, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x10, 0xF, 0x13121110, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x14, 0xF, 0x17161514, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x18, 0xF, 0x1B1A1918, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE0_0 + 0x1c, 0xF, 0x1F1E1D1C, 0, true},

    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x00, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x04, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x08, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x0C, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x10, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x14, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x18, 0xF, 0x0, 0, true},
    {true, 0, 0, 2, 0, AES_KEY_SHARE1_0 + 0x1c, 0xF, 0x0, 0, true},

    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x0, 0xF, 0x33221100, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x4, 0xF, 0x77665544, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0x8, 0xF, 0xBBAA9988, 0, true},
    {true, 0, 0, 2, 0, AES_DATA_IN_0 + 0xC, 0xF, 0xFFEEDDCC, 0, true},

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
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},

    // Clear
    {true, 0, 0, 2, 0, AES_TRIGGER, 0xF, 0x1E, 0, true},  // clear
    {true, 4, 0, 2, 0, AES_STATUS, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x0, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x4, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0x8, 0xF, 0x0, 0, true},
    {true, 4, 0, 2, 0, AES_DATA_OUT_0 + 0xC, 0xF, 0x0, 0, true},
};

static const int num_responses_max = 1 + 18 + 18 + 5;
static const EXP_RESP tl_o_exp_resp[num_responses_max] = {
    {1 << AES_STATUS_IDLE_OFFSET,
     1 << AES_STATUS_IDLE_OFFSET},  // status shows idle
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0xFFFFFFFF, 0xD8E0C469},
    {0xFFFFFFFF, 0x30047B6A},
    {0xFFFFFFFF, 0x80B7CDD8},
    {0xFFFFFFFF, 0x5AC5B470},
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0xFFFFFFFF, 0xA47CA9DD},
    {0xFFFFFFFF, 0xE0DF4C86},
    {0xFFFFFFFF, 0xA070AF6E},
    {0xFFFFFFFF, 0x91710DEC},
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {0x0, 0x0},                             // don't care
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     1 << AES_STATUS_OUTPUT_VALID_OFFSET},  // status shows output valid
    {0xFFFFFFFF, 0xCAB7A28E},
    {0xFFFFFFFF, 0xBF456751},
    {0xFFFFFFFF, 0x9049FCEA},
    {0xFFFFFFFF, 0x8960494B},
    {1 << AES_STATUS_OUTPUT_VALID_OFFSET,
     0},  // status shows output valid no longer valid

    {1 << AES_STATUS_IDLE_OFFSET,
     1 << AES_STATUS_IDLE_OFFSET},  // status shows idle
    {0x0, 0x0},                     // data_out0 cleared to random value
    {0x0, 0x0},                     // data_out1 cleared to random value
    {0x0, 0x0},                     // data_out2 cleared to random value
    {0x0, 0x0},                     // data_out3 cleared to random value
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_1_H_
