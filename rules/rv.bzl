# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helpers for transitioning to the RISC-V target."""

load("//hw/top:defs.bzl", "ALL_TOPS")
load("//rules/opentitan:hw.bzl", "get_top_attr")

OPENTITAN_BASE_PLATFORM = "//sw/target:opentitan_base_platform"
OPENTITAN_CPU = "@platforms//cpu:riscv32"

def _opentitan_transition_impl(settings, attr):
    # FIXME If transition composition were supported [1], the platform
    # transition would better be expressed as a transition, defined in
    # //hw/top. Instead, we have to reimplement some details of the top
    # selection here.
    # [1] https://github.com/bazelbuild/bazel/discussions/22019

    # Use the requested platform if specified.
    if attr.platform:
        platform = attr.platform
        # Otherwise use the top's specified platform.

    else:
        platform = None
        for top in ALL_TOPS:
            if settings["//hw/top"] == top.name:
                platform = get_top_attr(top, "platform", required = False, default = OPENTITAN_BASE_PLATFORM)
        if platform == None:
            fail("The requested top is not listed in ALL_TOPS")

    print("setting platform to", platform)
    return {
        "//command_line_option:platforms": platform,
        "//hw/bitstream/universal:rom": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:otp": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:env": "//hw/bitstream/universal:none",
    }

opentitan_transition = transition(
    implementation = _opentitan_transition_impl,
    inputs = [
        "//command_line_option:copt",
        "//hw/top",
    ],
    outputs = [
        "//command_line_option:platforms",
        "//hw/bitstream/universal:rom",
        "//hw/bitstream/universal:otp",
        "//hw/bitstream/universal:env",
    ],
)

def rv_rule(**kwargs):
    """
    A wrapper over rule() for painlessly creating rules that trigger the
    opentitan transition.
    """

    attrs = kwargs.pop("attrs", {})
    if "platform" not in attrs:
        attrs["platform"] = attr.string()
    attrs["_allowlist_function_transition"] = attr.label(
        default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
    )

    return rule(
        cfg = opentitan_transition,
        attrs = attrs,
        **kwargs
    )
