# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

CONST = struct(
    ROM_EXT = 0x4552544f,
    OWNER = 0x3042544f,
    TRUE = 0x739,
    FALSE = 0x1d4,
)

_DEFAULT_USAGE = 0xa5a5a5a5
_SEL_DEVICE_ID = 1
_SEL_MANUF_STATE_CREATOR = (1 << 8)
_SEL_MANUF_STATE_OWNER = (1 << 9)
_SEL_LIFE_CYCLE_STATE = (1 << 10)
_HEXSTR = "0123456789abcdef"

def _hex(i):
    # First "cast" i to a 32-bit unsigned int
    i &= 0xFFFFFFFF
    r = "0x"
    r += _HEXSTR[(i >> 28) & 0xF]
    r += _HEXSTR[(i >> 24) & 0xF]
    r += _HEXSTR[(i >> 20) & 0xF]
    r += _HEXSTR[(i >> 16) & 0xF]
    r += _HEXSTR[(i >> 12) & 0xF]
    r += _HEXSTR[(i >> 8) & 0xF]
    r += _HEXSTR[(i >> 4) & 0xF]
    r += _HEXSTR[(i >> 0) & 0xF]
    return r

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
        mf["binding_value"] = _hex(ctx.attr.binding_value)

    # The selector_bits are set based on the values of the usage_constraints.
    uc = {}
    selector_bits = 0
    device_id = list(ctx.attr.device_id)
    if len(device_id) > 8:
        fail("The device_id must be 8 words or fewer.")

    # Extend the device_id to 8 words, then set the selector_bits for each
    # non-default word.
    if len(device_id) < 8:
        device_id.extend([_DEFAULT_USAGE] * (8 - len(device_id)))
    for i, d in enumerate(device_id):
        if d != _DEFAULT_USAGE:
            selector_bits |= _SEL_DEVICE_ID << i
        device_id[i] = _hex(d)
    uc["device_id"] = device_id

    # Set the selector bits for the remaining non-default values.
    if ctx.attr.manuf_state_creator:
        uc["manuf_state_creator"] = _hex(ctx.attr.manuf_state_creator)
        selector_bits |= _SEL_MANUF_STATE_CREATOR
    else:
        uc["manuf_state_creator"] = _hex(_DEFAULT_USAGE)

    if ctx.attr.manuf_state_owner:
        uc["manuf_state_owner"] = _hex(ctx.attr.manuf_state_owner)
        selector_bits |= _SEL_MANUF_STATE_OWNER
    else:
        uc["manuf_state_owner"] = _hex(_DEFAULT_USAGE)

    if ctx.attr.life_cycle_state:
        uc["life_cycle_state"] = _hex(ctx.attr.life_cycle_state)
        selector_bits |= _SEL_LIFE_CYCLE_STATE
    else:
        uc["life_cycle_state"] = _hex(_DEFAULT_USAGE)

    # If the user supplied selector_bits, check if they make sense.
    if ctx.attr.selector_bits:
        # If they don't match, fail unless explicitly permitted to set a
        # bad value.
        if ctx.attr.selector_bits != selector_bits and ctx.attr.selector_mismatch_is_failure:
            fail("User provided selector_bits don't match computed selector_bits")
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

manifest = rule(
    implementation = _manifest_impl,
    attrs = {
        "signature": attr.string(doc = "Image signature as a hex-encoded string"),
        "modulus": attr.string(doc = "Signing key modulus as a hex-encoded string"),
        "selector_bits": attr.int(doc = "Usage constraint selector bits"),
        "selector_mismatch_is_failure": attr.bool(default = True, doc = "A mismatch in computed selector bits is a failure"),
        "device_id": attr.int_list(doc = "Usage constraint device ID"),
        "manuf_state_creator": attr.int(doc = "Usage constraint for silicon creator manufacturing status"),
        "manuf_state_owner": attr.int(doc = "Usage constraint for silicon owner manufacturing status"),
        "life_cycle_state": attr.int(doc = "Usage constraint for life cycle status"),
        "address_translation": attr.int(doc = "Whether this image uses address translation"),
        "identifier": attr.int(doc = "Manifest identifier"),
        "length": attr.int(doc = "Length of this image"),
        "version_major": attr.int(doc = "Image major version"),
        "version_minor": attr.int(doc = "Image minor version"),
        "security_version": attr.int(doc = "Security version for anti-rollback protection"),
        "timestamp": attr.int(doc = "Unix timestamp of the image"),
        "binding_value": attr.int_list(doc = "Binding value used by key manager to derive secrets"),
        "max_key_version": attr.int(doc = "Maximum allowed version for keys generated at the next boot stage"),
        "code_start": attr.int(doc = "Start offset of the executable region in the image"),
        "code_end": attr.int(doc = "End offset of the executable region in the image"),
        "entry_point": attr.int(doc = "Offset of the first instruction in the image"),
    },
)
