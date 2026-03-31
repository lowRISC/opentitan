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
    }
}
