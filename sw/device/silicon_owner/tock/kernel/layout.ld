/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

MEMORY
{
  rom   (rx)  : ORIGIN = 0x20000000, LENGTH = 0x40000
  /* Support up to 0x2009_0000 for apps
   * and 0x2009_0000 to 0x2010_0000 is for flash storage.
   */
  prog  (rx)  : ORIGIN = 0x20040000, LENGTH = 0x60000
  ram   (!rx) : ORIGIN = 0x10000000, LENGTH = 0x20000
}

MPU_MIN_ALIGN = 1K;
SECTIONS {
    /*
     * The flash header needs to match what the boot ROM for OpenTitan is
     * expecting.  At the moment, it contains only the entry point, but it
     * will eventually contain the signature -- and (hopefully?!) some
     * versioning information to make it slightly easier to debug when the
     * boot ROM and Tock are out of sync with respect to the definition...
     */
    .manifest ORIGIN(rom):
    {
        /* sw/device/silicon_creator/lib/manifest.h */
        . = . + 384; /* signature */
        . = . + 4;   /* usage_constraints.selector_bits */
        . = . + 32;  /* usage_constraints.device_id */
        . = . + 4;   /* usage_constraints.manuf_state_creator */
        . = . + 4;   /* usage_constraints.manuf_state_owner */
        . = . + 4;   /* usage_constraints.life_cycle_state */
        . = . + 384; /* modulus */
        . = . + 4;   /* address_translation */
        . = . + 4;   /* identifier */
        . = . + 2;   /* manifest_version.minor */
        . = . + 2;   /* manifest_version.major */
        . = . + 4;   /* signed_region_end */
        . = . + 4;   /* length */
        . = . + 4;   /* version_major */
        . = . + 4;   /* version_minor */
        . = . + 4;   /* security_version */
        . = . + 4;   /* timestamp.low */
        . = . + 4;   /* timestamp.high */
        . = . + 32;  /* binding_value */
        . = . + 4;   /* max_key_version */
        . = . + 4;   /* code_start */
        . = . + 4;   /* code_end */
        LONG(_stext - ORIGIN(rom)); /* . = . + 4; entry_point */
        . = . + 128; /* extensions[16] {u32 identifier, u32 offset} */
        /* size = 1024 bytes */
    } > rom

    .vectors : ALIGN (256) {
      KEEP(*(.riscv.open_titan_trap_vectored));
    } > rom

}

INCLUDE sw/device/silicon_owner/tock/kernel/kernel_layout.ld
