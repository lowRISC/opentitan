/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

_rom_origin_value = DEFINED(_rom_origin) ? _rom_origin : 0;
MEMORY { ROM (RX): ORIGIN = _rom_origin_value, LENGTH = 256K }

SECTIONS {
    .text.libotcrypto : {
        _libotcrypto_start_ = .;

        *(.text*)
        *(.rodata*)
        *(.srodata*)

        . = ALIGN(4);

        _libotcrypto_end_ = .;
        _libotcrypto_hash_ = .;

        . = . + 48;

        /*
         * Internal anchor: This symbol is used internally by the cryptolib C code
         * to generate a PC-relative offset pointing to this exact address.
         * The host firmware must use its global linker script to place a pointer
         * to its state variable at this physical location.
         * See cryptolib_api.md for info.
         */
        _libotcrypto_tether_ = .;
    } > ROM

    .sdata2 : {
        *(.sdata2*);
    } > ROM
    ASSERT(SIZEOF(.sdata2) == 0, "Error: No .sdata2 allowed in cryptolib")

    .data : {
        *(.data*);
        *(.sdata*);
    } > ROM
    ASSERT(SIZEOF(.data) == 0, "Error: No .data allowed in cryptolib")

    .bss : {
        *(.bss*);
        *(.sbss*);
    } > ROM
    ASSERT(SIZEOF(.bss) == 0, "Error: No .bss allowed in cryptolib")
}
