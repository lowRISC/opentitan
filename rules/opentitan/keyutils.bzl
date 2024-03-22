# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "key_allowed_in_lc_state")

KeyInfo = provider(
    """Key Information.

    Used to capture all required information about a key.
    """,
    fields = {
        "key_info": "Info associated with the key.",
    },
)

def _key_sphincs_plus(ctx):
    key_obj = {
        "id": "sphincs_plus",
        "config": ctx.attr.config,
        "method": ctx.attr.method,
        "pub_key": ctx.file.pub_key.path,
        "type": ctx.attr.type,
    }
    if ctx.attr.private_key:
        key_obj["private_key"] = ctx.file.private_key.path
    return [KeyInfo(key_info = key_obj)]

key_sphincs_plus = rule(
    implementation = _key_sphincs_plus,
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

def _key_ecdsa(ctx):
    key_obj = {
        "id": "ecdsa",
        "config": ctx.attr.config,
        "method": ctx.attr.method,
        "pub_key": ctx.file.pub_key.path,
        "type": ctx.attr.type,
    }
    if ctx.attr.private_key:
        key_obj["private_key"] = ctx.file.private_key.path

    return [KeyInfo(key_info = key_obj)]

key_ecdsa = rule(
    implementation = _key_ecdsa,
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
        "method": attr.string(
            doc = "Mechanism used to access the key. Can be local or hsmtool.",
            values = ["local", "hsmtool"],
        ),
    },
)

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
