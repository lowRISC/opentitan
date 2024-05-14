/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


/* Licensed under the Apache License, Version 2.0 or the MIT License. */
/* SPDX-License-Identifier: Apache-2.0 OR MIT                         */
/* Copyright Tock Contributors 2023.                                  */

MEMORY
{
  rom_ext (r) : ORIGIN = 0x20000000, LENGTH = 0x10000
  /* rom is the region the kernel image occupies (a Tock convention required by
   * tock/boards/kernel_layout.ld) -- it is not the region the chip's ROM exists
   * in.
   */
  rom   (rx)  : ORIGIN = 0x20010000, LENGTH = 0x30000
  /* Support up to 0x200a_0000 for apps
   * and 0x200a_0000 to 0x2010_0000 is for flash storage.
   */
  prog  (rx)  : ORIGIN = 0x20040000, LENGTH = 0x60000
  fs    (r)   : ORIGIN = 0x200a0000, LENGTH = 0x60000
  /* The first 0x650 bytes of RAM are reserved for the boot
   * ROM, so we have to ignore that space.
   * See https://github.com/lowRISC/opentitan/blob/master/sw/device/silicon_creator/lib/base/static_critical.ld
   * for details
   */
  ram   (!rx) : ORIGIN = 0x10000650, LENGTH = 0x20000 - 0x650
}

SECTIONS {
    /* Export the start & end of SRAM and flash as symbols for setting
     * up the ePMP. Flash includes rom, prog and flash storage, such
     * that we can use a single NAPOT region. The .text section will
     * be made executable by a separate PMP region.
     */
    _sflash = ORIGIN(rom_ext);
    _skernel = ORIGIN(rom);
    _eflash = ORIGIN(fs) + LENGTH(fs);

    _ssram  = ORIGIN(ram) - 0x650;
    _esram  = ORIGIN(ram) + LENGTH(ram);

    .manifest ORIGIN(rom):
    {
        _manifest = .;
        /* see: sw/device/silicon_creator/lib/manifest.h */
        . += 384; /* rsa_signature */
        . += 4;   /* usage_constraints.selector_bits */
        . += 32;  /* usage_constraints.device_id */
        . += 4;   /* usage_constraints.manuf_state_creator */
        . += 4;   /* usage_constraints.manuf_state_owner */
        . += 4;   /* usage_constraints.life_cycle_state */
        . += 384; /* rsa_modulus */
        LONG(0x1d4); /* . = . + 4; address_translation (HardenedFalse) */
        . += 4;   /* identifier */
        SHORT(0x6c47); /* . = . + 2; manifest_version.minor */
        SHORT(0x71c3); /* . = . + 2; manifest_version.major */
        . += 4;   /* signed_region_end */
        . += 4;   /* length */
        . += 4;   /* version_major */
        . += 4;   /* version_minor */
        . += 4;   /* security_version */
        . += 8;   /* timestamp */
        . += 32;  /* binding_value */
        . += 4;   /* max_key_version */
        LONG(_stext - ORIGIN(rom)); /* . = . + 4; code_start */
        LONG(_etext - ORIGIN(rom)); /* . = . + 4; code_end */
        LONG(_stext - ORIGIN(rom)); /* . = . + 4; entry_point */
        /* manifest extension table */
        /* see: sw/device/silicon_creator/lib/base/chip.h */
        /* CHIP_MANIFEST_EXT_TABLE_COUNT = 15 */
        /* sizeof(manifest_ext_table_entry) = 8 */
        . += 120; /* manifest_ext_table */
    } > rom
}

ASSERT (((_etext - _manifest) > 0), "Error: PMP and Flash protection setup assumes _etext follows _manifest");
/* TODO(cfrantz): Fix the ld_library rule to allow include paths and avoid  */
/* having to specify an `external` path here */
INCLUDE external/tock/boards/kernel_layout.ld
