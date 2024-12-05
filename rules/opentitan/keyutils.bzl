# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:signing.bzl", "KeyInfo")
load("//rules:const.bzl", "CONST")
load("@bazel_skylib//lib:structs.bzl", "structs")

def _build_key_info_handler(id):
    """Return a handler that creates a KeyInfo provider.

    Args:
        id: Identifier used by the consumers of the provider to determine the key algorithm.
    Returns:
        A handler that creates a KeyInfo provider.
    """

    def key_info_handler(ctx):
        return [KeyInfo(
            id = id,
            config = ctx.attr.config,
            method = ctx.attr.method,
            pub_key = ctx.file.pub_key,
            private_key = ctx.file.private_key,
            type = ctx.attr.type,
        )]

    return key_info_handler

key_sphincs_plus = rule(
    implementation = _build_key_info_handler("sphincs_plus"),
    attrs = {
        "pub_key": attr.label(
            allow_single_file = [".pem"],
            doc = "Public key in pem format.",
        ),
        "private_key": attr.label(
            allow_single_file = [".pem"],
            doc = "Private key in pem format.",
        ),
        "type": attr.string(
            default = "TestKey",
            doc = "The type of the key. Can be TestKey, DevKey or ProdKey.",
            values = ["TestKey", "DevKey", "ProdKey"],
        ),
        "config": attr.string(
            default = "Sha2128s",
            doc = "The config of the key. Can be Sha2128s[Q20][Prehash].",
            values = ["Sha2128s", "Sha2128sQ20", "Sha2128sPrehash", "Sha2128sQ20Prehash"],
        ),
        "method": attr.string(
            doc = "Mechanism used to access the key. Can be local or hsmtool.",
            values = ["local", "hsmtool"],
        ),
    },
)

key_ecdsa = rule(
    implementation = _build_key_info_handler("ecdsa"),
    attrs = {
        "pub_key": attr.label(
            allow_single_file = [".der"],
            doc = "Public key in DER format.",
        ),
        "private_key": attr.label(
            allow_single_file = [".der"],
            doc = "Private key in DER format.",
        ),
        "type": attr.string(
            default = "TestKey",
            doc = "The type of the key. Can be TestKey, DevKey or ProdKey.",
            values = ["TestKey", "DevKey", "ProdKey"],
        ),
        "config": attr.string(
            default = "EcdsaP256",
            doc = "The config of the key. Only EcdsaP256 is supported at the moment.",
            values = ["EcdsaP256"],
        ),
        # TODO(cfrantz, moidx, #22155): To support signing with opentitantool or
        # hsmtool, the `method` should be replaced with a `token` and `profile`
        # similar to the `keyset` rule.  The `token` is used to get access to
        # the appropriate PKCS11 resources (shared libs, config files, etc) and
        # the `profile` refers to a configuration in
        # $XDG_CONFIG_HOME/hsmtool/profiles.json that refers to the user's
        # physical token name and credentials.
        "method": attr.string(
            doc = "Mechanism used to access the key. Can be local or hsmtool.",
            values = ["local", "hsmtool"],
        ),
    },
)

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
                create_test_key("fake_ecdsa_test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256"),
            ],
            DEV = [
                create_dev_key("fake_ecdsa_dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:dev_key_0_ecdsa_p256"),
            ],
            PROD = [
                create_prod_key("fake_ecdsa_prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256"),
            ],
        ),
        SPX = struct(
            TEST = [
                create_test_key("fake_spx_test_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:test_key_0_spx"),
            ],
            DEV = [
                create_dev_key("fake_spx_dev_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:dev_key_0_spx"),
            ],
            PROD = [
                create_prod_key("fake_spx_prod_key_0", "@//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx"),
            ],
        ),
    ),
    # We can't expose real private keys publicly.
    REAL = None,
    UNAUTHORIZED = struct(
        SPX = [
            create_key_("spx_unauthorized_0", "@//sw/device/silicon_creator/rom/keys/unauthorized/spx:unauthorized_0_spx", []),
        ],
    ),
)

SILICON_OWNER_KEYS = struct(
    FAKE = struct(
        RSA = struct(
            TEST = [
                create_test_key("fake_rsa_rom_ext_test_key_0", "@//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_test_private_key_0"),
            ],
            DEV = [
                create_dev_key("fake_rsa_rom_ext_dev_key_0", "@//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_dev_private_key_0"),
            ],
            PROD = None,
        ),
        # We can't expose real private keys publicly.
        REAL = None,
        UNAUTHORIZED = None,
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

RSA_ONLY_ROM_EXT_KEY_STRUCTS = [
    create_key_struct(None, SILICON_OWNER_KEYS.FAKE.RSA.TEST[0], None),
    create_key_struct(None, SILICON_OWNER_KEYS.FAKE.RSA.DEV[0], None),
]
