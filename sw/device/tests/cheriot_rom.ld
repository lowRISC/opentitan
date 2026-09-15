/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * CHERIoT image linked as a first NVM stage, for the ROM to boot directly.
 */

INCLUDE OPENTITAN_TOP_MEMORY_LD

/* The first NVM stage starts at the base of NVM. */
_slot_start_address = ORIGIN(nvm);

/* Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of the slot. */
MEMORY {
  cheriot_creator_a(rx) : ORIGIN = _slot_start_address,
    LENGTH = LENGTH(nvm) / 2 - _nvm_slot_reserved_bytes
}
REGION_ALIAS("cheriot_nvm", cheriot_creator_a);

/*
 * DV log offset. Assigned per boot stage rather than per program: ROM uses
 * 0x0, so the stage it boots takes 0x10000.
 */
_dv_log_offset = 0x10000;

INCLUDE sw/device/tests/cheriot_common.ld
