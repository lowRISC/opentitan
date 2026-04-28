/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

_rom_origin_value = DEFINED(_rom_origin) ? _rom_origin : 0;
MEMORY { ROM (RX): ORIGIN = _rom_origin_value, LENGTH = 256K }

SECTIONS {
    .text : {
        _libotcrypto_start_ = .;
        *(.text)
        *(.text*)
        *(.rodata)
        *(.rodata*)

        . = ALIGN(4);
        _libotcrypto_end_ = .;

        /* Place the 48-byte hash block at the very end of the binary */
        KEEP(*(.libotcrypto_hash*))
    } > ROM

    .data : {
        *(.data*);
        *(.sdata*);
    } > ROM
    ASSERT(SIZEOF(.data) == 0, "No .data allowed")

    .bss : {
        *(.bss*);
        *(.sbss*);
    } > ROM
    ASSERT(SIZEOF(.bss) == 0, "No .bss allowed")

    /DISCARD/ : {
        *(.got*)
        *(.plt*)
        *(.iplt*)
        *(.rela*)
        *(.rel*)
    }
}
