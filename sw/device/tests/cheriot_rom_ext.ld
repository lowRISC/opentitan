/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * CHERIoT image linked as a Silicon Owner stage, for the ROM_EXT to boot.
 *
 * The slot geometry arrives as `--defsym` link flags from the execution
 * environment's `slot_spec`.
 */

INCLUDE OPENTITAN_TOP_MEMORY_LD

/* The owner slot starts after the fixed-size ROM_EXT region. */
_slot_start_address = ORIGIN(nvm) + _rom_ext_size;

/* Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of the slot. */
MEMORY {
  cheriot_owner_a(rx) : ORIGIN = _slot_start_address,
    LENGTH = LENGTH(nvm) / 2 - _rom_ext_size - _nvm_slot_reserved_bytes
}
REGION_ALIAS("cheriot_nvm", cheriot_owner_a);

/*
 * DV log offset. Assigned per boot stage rather than per program: ROM uses
 * 0x0 and the stage booted by ROM 0x10000, so an owner stage takes 0x20000.
 */
_dv_log_offset = 0x20000;

INCLUDE sw/device/tests/cheriot_common.ld
