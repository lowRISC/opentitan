# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load("@bazel_skylib//lib:structs.bzl", "structs")

def ecdsa_key_for_lc_state(key_structs, hw_lc_state):
    """Return a dictionary containing a single key that can be used in the given
    LC state. The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.ecdsa != None and key_allowed_in_lc_state(k.ecdsa, hw_lc_state))]
    if len(keys) == 0:
        fail("There are no ECDSA keys compatible with HW LC state {} in key structs".format(hw_lc_state))
    return {
        keys[0].ecdsa.label: keys[0].ecdsa.name,
    }

def rsa_key_for_lc_state(key_structs, hw_lc_state):
    """Return a dictionary containing a single key that can be used in the given
    LC state. The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.rsa != None and key_allowed_in_lc_state(k.rsa, hw_lc_state))]
    if len(keys) == 0:
        fail("There are no RSA keys compatible with HW LC state {} in key structs".format(hw_lc_state))
    return {
        keys[0].rsa.label: keys[0].rsa.name,
    }

def ecdsa_key_by_name(key_structs, nickname):
    """Return a dictionary containing a single key that matches the name given.

    The format of the dictionary is compatible with opentitan_test.

    Args:
        key_structs: List of key structs.
        nickname: Name of the key to search for.
    Returns:
        A dictionary containing the key.
    """
    keys = [k for k in key_structs if (k.ecdsa != None and k.ecdsa.name == nickname)]
    if len(keys) == 0:
        fail("There are no ECDSA keys compatible with name {} in key structs".format(nickname))
    return {
        keys[0].ecdsa.label: keys[0].ecdsa.name,
    }

def rsa_key_by_name(key_structs, nickname):
    """Return a dictionary containing a single key that matches the name given.
    The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.rsa != None and k.rsa.name == nickname)]
    if len(keys) == 0:
        fail("There are no RSA keys compatible with name {} in key structs".format(nickname))
    return {
        keys[0].rsa.label: keys[0].rsa.name,
    }

def spx_key_for_lc_state(key_structs, hw_lc_state):
    """Return a dictionary containing a single key that can be used in the given
    LC state. The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.spx != None and key_allowed_in_lc_state(k.spx, hw_lc_state))]
    if len(keys) == 0:
        fail("There are no SPX keys compatible with HW LC state {} in key structs".format(hw_lc_state))
    return {
        keys[0].spx.label: keys[0].spx.name,
    }

def spx_key_by_name(key_structs, nickname):
    """Return a dictionary containing a single key that matches the name given.
    The format of the dictionary is compatible with opentitan_test.
    """
    keys = [k for k in key_structs if (k.spx != None and k.spx.name == nickname)]
    if len(keys) == 0:
        fail("There are no SPX keys compatible with name {} in key structs".format(nickname))
    return {
        keys[0].spx.label: keys[0].spx.name,
    }

def key_allowed_in_lc_state(key, hw_lc_state_val):
    all_hw_lc_state_vals = structs.to_dict(CONST.LCV).values()
    if not hw_lc_state_val in all_hw_lc_state_vals:
        fail("Wrong life cycle state value: '{}', must be one of {}. Did you pass a string instead of the integer value?".format(hw_lc_state_val, all_hw_lc_state_vals))
    return hw_lc_state_val in key.hw_lc_states

def filter_key_structs_for_lc_state(key_structs, hw_lc_state):
    return [k for k in key_structs if (
        (not k.rsa or key_allowed_in_lc_state(k.rsa, hw_lc_state)) and
        (not k.ecdsa or key_allowed_in_lc_state(k.ecdsa, hw_lc_state)) and
        (not k.spx or key_allowed_in_lc_state(k.spx, hw_lc_state))
    )]

def create_key_(name, label, hw_lc_states):
    return struct(
        name = name,
        label = label,
        hw_lc_states = hw_lc_states,
    )

def create_test_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.RMA,
    ])

def create_dev_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.RMA,
        CONST.LCV.DEV,
    ])

def create_prod_key(name, label):
    return create_key_(name, label, [
        CONST.LCV.TEST_UNLOCKED0,
        CONST.LCV.TEST_UNLOCKED1,
        CONST.LCV.TEST_UNLOCKED2,
        CONST.LCV.TEST_UNLOCKED3,
        CONST.LCV.TEST_UNLOCKED4,
        CONST.LCV.TEST_UNLOCKED5,
        CONST.LCV.TEST_UNLOCKED6,
        CONST.LCV.TEST_UNLOCKED7,
        CONST.LCV.DEV,
        CONST.LCV.PROD,
        CONST.LCV.PROD_END,
        CONST.LCV.RMA,
    ])

def create_key_struct(ecdsa_key, rsa_key, spx_key):
    return struct(
        ecdsa = ecdsa_key,
        rsa = rsa_key,
        spx = spx_key,
    )

# Keys available in the repo
SILICON_CREATOR_KEYS = struct(
    FAKE = struct(
        ECDSA = struct(
            TEST = [
                create_test_key("test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset"),
            ],
            DEV = [
                create_dev_key("dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset"),
            ],
            PROD = [
                create_prod_key("prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset"),
            ],
        ),
        SPX = struct(
            TEST = [
                create_test_key("test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset"),
            ],
            DEV = [
                create_dev_key("dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset"),
            ],
            PROD = [
                create_prod_key("prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:spx_keyset"),
            ],
        ),
    ),
    # We can't expose real private keys publicly.
    REAL = None,
    UNAUTHORIZED = struct(
        SPX = [
            create_key_("unauthorized_key_0", "@//sw/device/silicon_creator/rom/keys/unauthorized/spx:spx_keyset", []),
        ],
    ),
)

ECDSA_ONLY_KEY_STRUCTS = [
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.TEST[0], None, None),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.DEV[0], None, None),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.PROD[0], None, None),
]

ECDSA_SPX_KEY_STRUCTS = [
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.TEST[0], None, SILICON_CREATOR_KEYS.FAKE.SPX.TEST[0]),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.DEV[0], None, SILICON_CREATOR_KEYS.FAKE.SPX.DEV[0]),
    create_key_struct(SILICON_CREATOR_KEYS.FAKE.ECDSA.PROD[0], None, SILICON_CREATOR_KEYS.FAKE.SPX.PROD[0]),
]
