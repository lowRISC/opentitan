// Generated register defines for hmac

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _HMAC_REG_DEFS_
#define _HMAC_REG_DEFS_

// Interrupt State Register
#define HMAC_INTR_STATE(id) (HMAC##id##_BASE_ADDR + 0x0)
#define HMAC_INTR_STATE_HMAC_DONE 0
#define HMAC_INTR_STATE_FIFO_FULL 1
#define HMAC_INTR_STATE_HMAC_ERR 2

// Interrupt Enable Register
#define HMAC_INTR_ENABLE(id) (HMAC##id##_BASE_ADDR + 0x4)
#define HMAC_INTR_ENABLE_HMAC_DONE 0
#define HMAC_INTR_ENABLE_FIFO_FULL 1
#define HMAC_INTR_ENABLE_HMAC_ERR 2

// Interrupt Test Register
#define HMAC_INTR_TEST(id) (HMAC##id##_BASE_ADDR + 0x8)
#define HMAC_INTR_TEST_HMAC_DONE 0
#define HMAC_INTR_TEST_FIFO_FULL 1
#define HMAC_INTR_TEST_HMAC_ERR 2

// HMAC Configuration register
#define HMAC_CFG(id) (HMAC##id##_BASE_ADDR + 0xc)
#define HMAC_CFG_HMAC_EN 0
#define HMAC_CFG_SHA_EN 1
#define HMAC_CFG_ENDIAN_SWAP 2
#define HMAC_CFG_DIGEST_SWAP 3

// HMAC command register
#define HMAC_CMD(id) (HMAC##id##_BASE_ADDR + 0x10)
#define HMAC_CMD_HASH_START 0
#define HMAC_CMD_HASH_PROCESS 1

// HMAC Status register
#define HMAC_STATUS(id) (HMAC##id##_BASE_ADDR + 0x14)
#define HMAC_STATUS_FIFO_EMPTY 0
#define HMAC_STATUS_FIFO_FULL 1
#define HMAC_STATUS_FIFO_DEPTH_MASK 0x1f
#define HMAC_STATUS_FIFO_DEPTH_OFFSET 4

// HMAC Error Code
#define HMAC_ERR_CODE(id) (HMAC##id##_BASE_ADDR + 0x18)

// Randomize internal secret registers.
#define HMAC_WIPE_SECRET(id) (HMAC##id##_BASE_ADDR + 0x1c)

// HMAC Secret Key
#define HMAC_KEY0(id) (HMAC##id##_BASE_ADDR + 0x20)

// HMAC Secret Key
#define HMAC_KEY1(id) (HMAC##id##_BASE_ADDR + 0x24)

// HMAC Secret Key
#define HMAC_KEY2(id) (HMAC##id##_BASE_ADDR + 0x28)

// HMAC Secret Key
#define HMAC_KEY3(id) (HMAC##id##_BASE_ADDR + 0x2c)

// HMAC Secret Key
#define HMAC_KEY4(id) (HMAC##id##_BASE_ADDR + 0x30)

// HMAC Secret Key
#define HMAC_KEY5(id) (HMAC##id##_BASE_ADDR + 0x34)

// HMAC Secret Key
#define HMAC_KEY6(id) (HMAC##id##_BASE_ADDR + 0x38)

// HMAC Secret Key
#define HMAC_KEY7(id) (HMAC##id##_BASE_ADDR + 0x3c)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST0(id) (HMAC##id##_BASE_ADDR + 0x40)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST1(id) (HMAC##id##_BASE_ADDR + 0x44)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST2(id) (HMAC##id##_BASE_ADDR + 0x48)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST3(id) (HMAC##id##_BASE_ADDR + 0x4c)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST4(id) (HMAC##id##_BASE_ADDR + 0x50)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST5(id) (HMAC##id##_BASE_ADDR + 0x54)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST6(id) (HMAC##id##_BASE_ADDR + 0x58)

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST7(id) (HMAC##id##_BASE_ADDR + 0x5c)

// Received Message Length in bits [31:0].
#define HMAC_MSG_LENGTH_LOWER(id) (HMAC##id##_BASE_ADDR + 0x60)

// Received Message Length in bits [63:32]
#define HMAC_MSG_LENGTH_UPPER(id) (HMAC##id##_BASE_ADDR + 0x64)

// Memory area: Message FIFO. Any address starts from offset 0x800 to 0xFFF
#define HMAC_MSG_FIFO(id) (HMAC##id##_BASE_ADDR + 0x800)
#define HMAC_MSG_FIFO_SIZE_WORDS 512
#define HMAC_MSG_FIFO_SIZE_BYTES 2048
#endif  // _HMAC_REG_DEFS_
// End generated register defines for hmac
