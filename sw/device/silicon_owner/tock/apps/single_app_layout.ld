/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Layout for the RISC-V 32 boards, used by the examples in this repository. */

TBF_HEADER_SIZE = 0x80;

FLASH_START = 0x20040000;
FLASH_LENGTH = 32M;

RAM_START = 0x10005000;
RAM_LENGTH = 512K;

/* TODO(cfrantz): Fix the ld_library rule to allow include paths and avoid  */
/* having to specify an `external` path here */
INCLUDE external/libtock/runtime/libtock_layout.ld
