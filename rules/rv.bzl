# Copyright lowRISC contributors.
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
    return {
        "//command_line_option:platforms": attr.platform,
        "//hw/bitstream/universal:rom": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:otp": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:env": "//hw/bitstream/universal:none",
    }

opentitan_transition = transition(
    implementation = _opentitan_transition_impl,
    inputs = [],
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
        attrs["platform"] = attr.string(default = OPENTITAN_PLATFORM)
    attrs["_allowlist_function_transition"] = attr.label(
        default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
    )

    return rule(
        cfg = opentitan_transition,
        attrs = attrs,
        **kwargs
    )
