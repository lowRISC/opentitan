// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_COMMON_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_COMMON_H_

#define AES_KEY0 0x0
#define AES_IV0 0x20
#define AES_DATA_IN0 0x30
#define AES_DATA_OUT0 0x40
#define AES_CONFIG 0x50
#define AES_TRIGGER 0x54
#define AES_STATUS 0x58

#define AES_CTRL_KEY_LEN_OFFSET 7
#define AES_CTRL_MANUAL_OPERATION_OFFSET 10

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_SEQUENCE_COMMON_H_
