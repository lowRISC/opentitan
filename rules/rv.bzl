# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helpers for transitioning to the RISC-V target."""

load("//hw/top:defs.bzl", "ALL_TOPS")
load("//rules/opentitan:hw.bzl", "get_top_attr")

def _opentitan_transition_impl(settings, attr):
    # FIXME This should really be expressed as the composition of two transitions
    # using `and_then`, but this only available in Bazel 9.

    # Use the requested platform if specified.
    if attr.platform:
        platform = attr.platform
    else:
        # Otherwise use the top's default platform.
        platform = None
        for top in ALL_TOPS:
            if settings["//hw/top"] == top.name:
                platforms = get_top_attr(top, "platforms", required = True)
                if attr.platform_key not in platforms:
                    # If the requested platform key cannot be found, fallback to the default key.
                    # We want to avoid turning this into an error because some queries could hit
                    # in this transition in unexpected configurations.
                    print("WARNING: top `{}` does not have a platform with key `{}`, falling back to default platform key".format(top.name, attr.platform_key))
                    platform = platforms[""]
                else:
                    platform = platforms[attr.platform_key]
        if platform == None:
            fail("The requested top is not listed in ALL_TOPS")

    coverage = settings["//command_line_option:collect_code_coverage"]
    if attr.collect_code_coverage != -1:
        coverage = bool(attr.collect_code_coverage)
    return {
        "//command_line_option:platforms": platform,
        "//command_line_option:copt": settings["//command_line_option:copt"],
        "//command_line_option:collect_code_coverage": coverage,
    }

opentitan_transition = transition(
    implementation = _opentitan_transition_impl,
    # In order to build the englishbreakfast binaries, we need to pass through
    # the `--copt` and `--features` flags:
    # - The copt flag defines a preprocessor symbol indicating englishbreakfast.
    # - The features flags turn off compiler support for CPU extensions not
    #   present in the englishbreakfast rv32i implementation.
    inputs = [
        "//command_line_option:copt",
        "//command_line_option:collect_code_coverage",
        "//hw/top",
    ],
    outputs = [
        "//command_line_option:platforms",
        "//command_line_option:copt",
        "//command_line_option:collect_code_coverage",
    ],
)

def rv_rule(**kwargs):
    """
    A wrapper over rule() for painlessly creating rules that trigger the
    opentitan transition.
    """

    attrs = kwargs.pop("attrs", {})
    if "platform" not in attrs:
        attrs["platform"] = attr.string(
            doc = "If set, the platform will be transitioned to the label specified in this attribute",
        )
    if "platform_key" not in attrs:
        attrs["platform_key"] = attr.string(
            doc = "If `platform` is not set, the platform will be derived from the selected top using its `platforms` attribute, using this attribute as the key",
        )
    if "collect_code_coverage" not in attrs:
        attrs["collect_code_coverage"] = attr.int(
            default = -1,
            doc = """Whether to collect coverage for this target.

            When set to -1 (the default), the decision is inherited from the global setting.
            When set to 0, coverage collection is always disabled for this target.
            When set to 1, coverage collection is always enabled for this target.
            """,
        )
    attrs["_allowlist_function_transition"] = attr.label(
        default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
    )

    return rule(
        cfg = opentitan_transition,
        attrs = attrs,
        **kwargs
    )
