# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helper functions for generating expected test signatures for sigverify_key_type tests."""

load("//rules/opentitan:defs.bzl", "DEFAULT_TEST_FAILURE_MSG")
load("//rules:const.bzl", "CONST", "hex_digits")
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV_LCV",
)
load("//rules/opentitan:keyutils.bzl", "key_allowed_in_lc_state")

# SPHINCS+ is disabled uncoditionally in these lifecycle states.
SPX_DISABLED_LC_STATES = [
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.TEST_UNLOCKED1,
    CONST.LCV.TEST_UNLOCKED2,
    CONST.LCV.TEST_UNLOCKED3,
    CONST.LCV.TEST_UNLOCKED4,
    CONST.LCV.TEST_UNLOCKED5,
    CONST.LCV.TEST_UNLOCKED6,
    CONST.LCV.TEST_UNLOCKED7,
]

def ecdsa_exit_failure(lc_state_val, key):
    """Generate expected failure test signature.

    Args:
        lc_state_val: Lifecycle state value.
        key: Key object. Must have ecdsa key.
    Returns:
        Expected failure test signature to be used in opentitan_test.
    """
    return MSG_PASS if not key_allowed_in_lc_state(
        key.ecdsa,
        lc_state_val,
    ) else MSG_TEMPLATE_BFV_LCV.format(
        hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_KEY),
        hex_digits(lc_state_val),
    )

def ecdsa_exit_success(lc_state_val, key):
    """Generate expected success test signature.

    Args:
        lc_state_val: Lifecycle state value.
        key: Key object. Must have ecdsa key.
    Returns:
        Expected success test signature to be used in opentitan_test.
    """
    return MSG_PASS if key_allowed_in_lc_state(
        key.ecdsa,
        lc_state_val,
    ) else MSG_TEMPLATE_BFV_LCV.format(
        hex_digits(CONST.BFV.SIGVERIFY.BAD_ECDSA_KEY),
        hex_digits(lc_state_val),
    )

def spx_exit_failure(lc_state_val, key):
    """Generate expected failure test signature.

    Returns `MSG_DEFAULT_TEST_FAILURE_MSGPASS` if `lc_state_val` is in
    `SPX_DISABLED_LC_STATES`. This is because in this case ECDSA signature
    verification is expected to pass.

    Args:
        lc_state_val: Lifecycle state value.
        key: Key object. Must have spx key.
    Returns:
        Expected failure test signature to be used in opentitan_test.
    """
    if lc_state_val in SPX_DISABLED_LC_STATES:
        return DEFAULT_TEST_FAILURE_MSG
    return MSG_PASS if not key_allowed_in_lc_state(
        key.ecdsa,
        lc_state_val,
    ) else MSG_TEMPLATE_BFV_LCV.format(
        hex_digits(CONST.BFV.SIGVERIFY.BAD_SPX_KEY),
        hex_digits(lc_state_val),
    )

def spx_exit_success(lc_state_val, key):
    """Generate expected success test signature.

    Returns `MSG_PASS` if `lc_state_val` is in `SPX_DISABLED_LC_STATES`. This
    is because in this case ECDSA signature verification is expected to
    pass.

    Args:
        lc_state_val: Lifecycle state value.
        key: Key object. Must have spx key.
    Returns:
        Expected success test signature to be used in opentitat_test.
    """
    if lc_state_val in SPX_DISABLED_LC_STATES:
        return MSG_PASS
    return MSG_PASS if key_allowed_in_lc_state(
        key.ecdsa,
        lc_state_val,
    ) else MSG_TEMPLATE_BFV_LCV.format(
        hex_digits(CONST.BFV.SIGVERIFY.BAD_SPX_KEY),
        hex_digits(lc_state_val),
    )
