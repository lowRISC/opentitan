# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load("@bazel_skylib//lib:structs.bzl", "structs")

_ALL_LC_STATE_VALS = structs.to_dict(CONST.LCV).values()
_SKIP_LC_STATE_VALS = [
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.DEV,
]
_REM_LC_STATE_VALS = [
    lc_state_val
    for lc_state_val in _ALL_LC_STATE_VALS
    if lc_state_val not in _SKIP_LC_STATE_VALS
]

def maybe_skip_in_ci(lc_state_val):
    if lc_state_val in _SKIP_LC_STATE_VALS:
        return ["skip_in_ci"]
    if lc_state_val in _REM_LC_STATE_VALS:
        return []
    fail("Life cycle state value {} is not in {}", lc_state_val, _ALL_LC_STATE_VALS)
