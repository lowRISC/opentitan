# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Helpers for transitioning to the RISC-V target."""

OPENTITAN_CPU = "@platforms//cpu:riscv32"
OPENTITAN_PLATFORM = "@crt//platforms/riscv32:opentitan"

# This constant holds a dictionary of per-device dependencies which are used to
# generate slightly different binaries for each hardware target, including two
# simulation platforms (DV and Verilator), and two FPGA platforms (CW305
# and CW310).
PER_DEVICE_DEPS = {
    "sim_verilator": ["//sw/device/lib/arch:sim_verilator"],
    "sim_dv": ["//sw/device/lib/arch:sim_dv"],
    "fpga_cw305": ["//sw/device/lib/arch:fpga_cw305"],
    "fpga_cw310": ["//sw/device/lib/arch:fpga_cw310"],
}

def _opentitan_transition_impl(settings, attr):
    top = settings["//hw/top:top"]
    copt = settings["//command_line_option:copt"]
    features = settings["//command_line_option:features"]
    # In order to build the englishbreakfast binaries, we need to pass through
    # the `--copt` and `--features` flags:
    # - The copt flag defines a preprocessor symbol indicating englishbreakfast.
    # - The features flags turn off compiler support for CPU extensions not
    #   present in the englishbreakfast rv32i implementation.
    if top == "englishbreakfast":
        copt.append("-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_")
        features.append("-rv32_bitmanip")

    return {
        "//command_line_option:platforms": attr.platform,
        "//command_line_option:copt": copt,
        "//command_line_option:features": features,
        "//hw/bitstream/universal:rom": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:otp": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:env": "//hw/bitstream/universal:none",
    }

opentitan_transition = transition(
    implementation = _opentitan_transition_impl,
    # In order to set the right compiler options for the top, we need to read
    # the top configuration from //hw/top. We also pass selected copts and features
    # unmodified.
    inputs = [
        "//hw/top:top",
        "//command_line_option:copt",
        "//command_line_option:features",
    ],
    outputs = [
        "//command_line_option:platforms",
        "//command_line_option:copt",
        "//command_line_option:features",
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
        attrs["platform"] = attr.string(default = OPENTITAN_PLATFORM)
    attrs["_allowlist_function_transition"] = attr.label(
        default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
    )

    return rule(
        cfg = opentitan_transition,
        attrs = attrs,
        **kwargs
    )
