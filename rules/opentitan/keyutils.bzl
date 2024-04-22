# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "key_allowed_in_lc_state")
load("//rules:signing.bzl", "KeyInfo")

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
            default = "Shake128s",
            doc = "The config of the key. Can be Shake128s or Shake128sQ20.",
            values = ["Shake128s", "Shake128sQ20"],
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
