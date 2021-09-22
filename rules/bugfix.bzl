# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def find_cc_toolchain(ctx):
    """
    Returns the current `CcToolchainInfo`.

    Args:
      ctx: The rule context for which to find a toolchain.

    Returns:
      A CcToolchainInfo.
    """

    # Check the incompatible flag for toolchain resolution.
    if hasattr(cc_common, "is_cc_toolchain_resolution_enabled_do_not_use") and cc_common.is_cc_toolchain_resolution_enabled_do_not_use(ctx = ctx):
        if "@rules_cc//cc:toolchain_type" in ctx.toolchains:
            return ctx.toolchains["@rules_cc//cc:toolchain_type"]

        # Fall back to the legacy implicit attribute lookup.
    elif hasattr(ctx.attr, "_cc_toolchain"):
        return ctx.attr._cc_toolchain[cc_common.CcToolchainInfo]

    # We didn't find anything.
    fail("In order to use find_cc_toolchain, your rule has to depend on C++ toolchain. See find_cc_toolchain.bzl docs for details.")
