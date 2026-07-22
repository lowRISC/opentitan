# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

EARLGREY_SLOTS_NORMAL = {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x10000",
    "owner_slot_b": "0x90000",
    "rom_ext_size": "0x10000",
    "rom_ext_protected_size": "0x10000",
}

EARLGREY_SLOTS_COVERAGE = {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x20000",
    "owner_slot_b": "0xa0000",
    "rom_ext_size": "0x20000",
    "rom_ext_protected_size": "0x20000",
}

EARLGREY_SLOTS = select({
    "@lowrisc_opentitan//rules/coverage:enabled": EARLGREY_SLOTS_COVERAGE,
    "//conditions:default": EARLGREY_SLOTS_NORMAL,
})

EARLGREY_MLDSA_SLOTS_NORMAL = {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x16000",
    "owner_slot_b": "0x96000",
    "rom_ext_size": "0x16000",
    "rom_ext_protected_size": "0x14000",
}

EARLGREY_MLDSA_SLOTS_COVERAGE = {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x2a000",
    "owner_slot_b": "0xaa000",
    "rom_ext_size": "0x2a000",
    "rom_ext_protected_size": "0x28000",
}

EARLGREY_MLDSA_SLOTS = select({
    "@lowrisc_opentitan//rules/coverage:enabled": EARLGREY_MLDSA_SLOTS_COVERAGE,
    "//conditions:default": EARLGREY_MLDSA_SLOTS_NORMAL,
})
