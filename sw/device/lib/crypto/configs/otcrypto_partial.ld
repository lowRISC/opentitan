/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

SECTIONS {
    .text.libotcrypto : {
        _libotcrypto_start_ = .;

        *(.text*)
        *(.rodata*)
        *(.srodata*)

        . = ALIGN(4);

        _libotcrypto_end_ = .;
        _libotcrypto_hash_ = .;

        . = . + 48; /* Reserved for the hash */

        /*
         * Internal anchor: This symbol is used internally by the cryptolib C code
         * to generate a PC-relative offset pointing to this exact address.
         * The host firmware must use its global linker script to place a pointer
         * to its state variable at this physical location.
         * See cryptolib_api.md for info.
         */
        _libotcrypto_tether_ = .;
    }
}
