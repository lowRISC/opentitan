# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

EARLGREY_SLOTS_COMMON = {
    "flash_rom_slot": "0xf0000",
    "flash_rom_size": "0x10000",
    "flash_rom_magic": "0xfff88",
}

EARLGREY_SLOTS_NORMAL = EARLGREY_SLOTS_COMMON | {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x10000",
    "owner_slot_b": "0x90000",
    "rom_ext_size": "0x10000",
}

EARLGREY_SLOTS_COVERAGE = EARLGREY_SLOTS_COMMON | {
    "rom_ext_slot_a": "0x0",
    "rom_ext_slot_b": "0x80000",
    "owner_slot_a": "0x20000",
    "owner_slot_b": "0xa0000",
    "rom_ext_size": "0x20000",
}

EARLGREY_SLOTS = select({
    "@lowrisc_opentitan//rules/coverage:enabled": EARLGREY_SLOTS_COVERAGE,
    "//conditions:default": EARLGREY_SLOTS_NORMAL,
})
