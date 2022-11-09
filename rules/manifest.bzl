# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")

_SEL_DEVICE_ID = 1
_SEL_MANUF_STATE_CREATOR = (1 << 8)
_SEL_MANUF_STATE_OWNER = (1 << 9)
_SEL_LIFE_CYCLE_STATE = (1 << 10)

def _hex(v):
    """Expects v to be an int or a hex-encoded string."""
    if type(v) == "string":
        v = int(v, base = 16)
    return "0x{}".format(hex(v))

def _manifest_impl(ctx):
    mf = {}

    # All the easy parameters are simple assignments
    if ctx.attr.signature:
        mf["signature"] = _hex(ctx.attr.signature)
    if ctx.attr.modulus:
        mf["modulus"] = _hex(ctx.attr.modulus)
    if ctx.attr.identifier:
        mf["identifier"] = _hex(ctx.attr.identifier)
    if ctx.attr.length:
        mf["length"] = _hex(ctx.attr.length)
    if ctx.attr.version_major:
        mf["version_major"] = _hex(ctx.attr.version_major)
    if ctx.attr.version_minor:
        mf["version_minor"] = _hex(ctx.attr.version_minor)
    if ctx.attr.security_version:
        mf["security_version"] = _hex(ctx.attr.security_version)
    if ctx.attr.timestamp:
        mf["timestamp"] = _hex(ctx.attr.timestamp)
    if ctx.attr.max_key_version:
        mf["max_key_version"] = _hex(ctx.attr.max_key_version)
    if ctx.attr.code_start:
        mf["code_start"] = _hex(ctx.attr.code_start)
    if ctx.attr.code_end:
        mf["code_end"] = _hex(ctx.attr.code_end)
    if ctx.attr.entry_point:
        mf["entry_point"] = _hex(ctx.attr.entry_point)

    # Address Translation is a bool, but encoded as an int so we can have
    # a special value mean "unset" and so we can set to non-standard values
    # for testing.
    if ctx.attr.address_translation:
        mf["address_translation"] = _hex(ctx.attr.address_translation)

    # The binding_value, if provided, must be exactly 8 words.
    if ctx.attr.binding_value:
        if len(ctx.attr.binding_value) != 8:
            fail("The binding_value must be exactly 8 words.")
        mf["binding_value"] = [_hex(v) for v in ctx.attr.binding_value]

    # The selector_bits are set based on the values of the usage_constraints.
    uc = {}
    selector_bits = 0
    device_id = list(ctx.attr.device_id)
    if len(device_id) > 8:
        fail("The device_id must be 8 words or fewer.")

    # Extend the device_id to 8 words, then set the selector_bits for each
    # non-default word.
    if len(device_id) < 8:
        device_id.extend([CONST.DEFAULT_USAGE_CONSTRAINTS] * (8 - len(device_id)))
    for i, d in enumerate(device_id):
        if _hex(d) != _hex(CONST.DEFAULT_USAGE_CONSTRAINTS):
            selector_bits |= _SEL_DEVICE_ID << i
        device_id[i] = _hex(d)
    uc["device_id"] = device_id

    # Set the selector bits for the remaining non-default values.
    if ctx.attr.manuf_state_creator:
        uc["manuf_state_creator"] = _hex(ctx.attr.manuf_state_creator)
        selector_bits |= _SEL_MANUF_STATE_CREATOR
    else:
        uc["manuf_state_creator"] = _hex(CONST.DEFAULT_USAGE_CONSTRAINTS)

    if ctx.attr.manuf_state_owner:
        uc["manuf_state_owner"] = _hex(ctx.attr.manuf_state_owner)
        selector_bits |= _SEL_MANUF_STATE_OWNER
    else:
        uc["manuf_state_owner"] = _hex(CONST.DEFAULT_USAGE_CONSTRAINTS)

    if ctx.attr.life_cycle_state:
        uc["life_cycle_state"] = _hex(ctx.attr.life_cycle_state)
        selector_bits |= _SEL_LIFE_CYCLE_STATE
    else:
        uc["life_cycle_state"] = _hex(CONST.DEFAULT_USAGE_CONSTRAINTS)

    # If the user supplied selector_bits, check if they make sense.
    if ctx.attr.selector_bits:
        # If they don't match, fail unless explicitly permitted to set a
        # bad value.
        if int(ctx.attr.selector_bits, base = 16) != selector_bits and ctx.attr.selector_mismatch_is_failure:
            fail("User provided selector_bits ({}) don't match computed selector_bits ({})".format(ctx.attr.selector_bits, _hex(selector_bits)))
        uc["selector_bits"] = _hex(ctx.attr.selector_bits)
    else:
        uc["selector_bits"] = _hex(selector_bits)

    mf["usage_constraints"] = uc

    file = ctx.actions.declare_file("{}.json".format(ctx.attr.name))
    ctx.actions.write(file, json.encode_indent(mf))
    return DefaultInfo(
        files = depset([file]),
        data_runfiles = ctx.runfiles(files = [file]),
    )

_manifest = rule(
    implementation = _manifest_impl,
    # Manifest attrs are supplied as strings due to Bazel limiting int types to 32-bit signed integers
    attrs = {
        "signature": attr.string(doc = "Image signature as a hex-encoded string"),
        "modulus": attr.string(doc = "Signing key modulus as a hex-encoded string"),
        "selector_bits": attr.string(doc = "Usage constraint selector bits as a hex-encoded string"),
        "selector_mismatch_is_failure": attr.bool(default = True, doc = "A mismatch in computed selector bits is a failure"),
        "device_id": attr.string_list(doc = "Usage constraint device ID as a hex-encoded string"),
        "manuf_state_creator": attr.string(doc = "Usage constraint for silicon creator manufacturing status as a hex-encoded string"),
        "manuf_state_owner": attr.string(doc = "Usage constraint for silicon owner manufacturing status as a hex-encoded string"),
        "life_cycle_state": attr.string(doc = "Usage constraint for life cycle status as a hex-encoded string"),
        "address_translation": attr.string(doc = "Whether this image uses address translation as a hex-encoded string"),
        "identifier": attr.string(doc = "Manifest identifier as a hex-encoded string"),
        "length": attr.string(doc = "Length of this image as a hex-encoded string"),
        "version_major": attr.string(doc = "Image major version as a hex-encoded string"),
        "version_minor": attr.string(doc = "Image minor version as a hex-encoded string"),
        "security_version": attr.string(doc = "Security version for anti-rollback protection as a hex-encoded string"),
        "timestamp": attr.string(doc = "Unix timestamp of the image as a hex-encoded string"),
        "binding_value": attr.string_list(doc = "Binding value used by key manager to derive secrets as a hex-encoded string"),
        "max_key_version": attr.string(doc = "Maximum allowed version for keys generated at the next boot stage as a hex-encoded string"),
        "code_start": attr.string(doc = "Start offset of the executable region in the image as a hex-encoded string"),
        "code_end": attr.string(doc = "End offset of the executable region in the image as a hex-encoded string"),
        "entry_point": attr.string(doc = "Offset of the first instruction in the image as a hex-encoded string"),
    },
)

def manifest(d):
    _manifest(**d)
    return d["name"]
