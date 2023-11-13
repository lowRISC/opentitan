# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Transition rules for accessing the host platform

This file contains transition rules for accessing the host platform's
configuration. Primarily, this provides transitions for rules where a tool runs
on the host but the target configuration is not the host. For rules where
the host configuration is not adequate, toolchains should be used instead.
"""

def _host_tools_transition_impl(settings, attr):
    """Returns a dictionary with the platforms command line option set to host.

    This transition is used for building host tools, passing through all build
    settings specified on the command line.
    """
    ret = {
        "//command_line_option:platforms": "@local_config_platform//:host",
        "//command_line_option:copt": settings["//command_line_option:copt"],
        "//command_line_option:features": settings["//command_line_option:features"],
        "//hw/bitstream/universal:rom": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:otp": "//hw/bitstream/universal:none",
        "//hw/bitstream/universal:env": "//hw/bitstream/universal:none",
    }
    return ret

host_tools_transition = transition(
    implementation = _host_tools_transition_impl,
    inputs = [
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
