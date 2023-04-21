# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")

# ROM/ROM_EXT key roles
KEY_ROLE = struct(
    DEV = "dev",
    TEST = "test",
    PROD = "prod",
    UNAUTHORIZED = "unauthorized",
)

# key mapping for earlgrey, as described in hw/top_earlgrey/doc/design/README.md
EARLGREY_KEYMAP = struct(
    name = "earlgrey",
    slots = [
        # key_name: (rom slot index, key role)
        ("test_key_0", KEY_ROLE.TEST),
        ("dev_key_0", KEY_ROLE.DEV),
        ("prod_key_0", KEY_ROLE.PROD),
    ],
)

def keymap_for_keyset(keymap, keyset):
    new_slots = [(keyset + "_" + name, role) for (name, role) in keymap.slots]
    return struct(name = keymap.name, slots = new_slots)

# Return a list of all key names that appear is a map
def get_all_keys(keymap):
    return [name for (name, _) in keymap.slots]

# Return the list of slots, in which they appear in the ROM, which is a list of key names
def get_rom_slots(keymap):
    return [name for (name, _) in keymap.slots]

# Return a dictionary, indexed by KEY_ROLEs, of keys that are mapped to this role
def get_keys_for_roles(keymap):
    res = {}
    for (name, role) in keymap.slots:
        res[role] = res.get(role, []) + [name]
    return res

# List of usable key roles for each life cycle
KEY_ROLES_FOR_LC = {
    CONST.LCV.TEST_UNLOCKED0: [KEY_ROLE.TEST, KEY_ROLE.PROD],
    CONST.LCV.DEV: [KEY_ROLE.DEV, KEY_ROLE.PROD],
    CONST.LCV.PROD: [KEY_ROLE.PROD],
    CONST.LCV.PROD_END: [KEY_ROLE.PROD],
    CONST.LCV.RMA: [KEY_ROLE.TEST, KEY_ROLE.PROD],
}

# Return a dictionary, index by CONST.LCV, of acceptable keys that can be used in
# that life cycle given the role to which they are mapped
def get_keys_for_lcv(keymap):
    keys_for_role = get_keys_for_roles(keymap)
    res = {
        lcv: [x for role in roles for x in keys_for_role[role]]
        for (lcv, roles) in KEY_ROLES_FOR_LC.items()
    }
    return res
