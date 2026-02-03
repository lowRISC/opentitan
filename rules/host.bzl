# Copyright lowRISC contributors (OpenTitan project).
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
        "@lowrisc_opentitan//command_line_option:platforms": "@local_config_platform//:host",
        "@lowrisc_opentitan//command_line_option:copt": settings["@lowrisc_opentitan//command_line_option:copt"],
        "@lowrisc_opentitan//command_line_option:features": settings["@lowrisc_opentitan//command_line_option:features"],
        "@lowrisc_opentitan//hw/bitstream/universal:rom": "@lowrisc_opentitan//hw/bitstream/universal:none",
        "@lowrisc_opentitan//hw/bitstream/universal:otp": "@lowrisc_opentitan//hw/bitstream/universal:none",
        "@lowrisc_opentitan//hw/bitstream/universal:env": "@lowrisc_opentitan//hw/bitstream/universal:none",
        # WARNING This is a horrible hack: when we transition to host, we pretend
        # that this is earlgrey so opentitantool can compile...
        "@lowrisc_opentitan//hw/top": "earlgrey",
    }
    return ret

host_tools_transition = transition(
    implementation = _host_tools_transition_impl,
    inputs = [
        "@lowrisc_opentitan//command_line_option:copt",
        "@lowrisc_opentitan//command_line_option:features",
    ],
    outputs = [
        "@lowrisc_opentitan//command_line_option:platforms",
        "@lowrisc_opentitan//command_line_option:copt",
        "@lowrisc_opentitan//command_line_option:features",
        "@lowrisc_opentitan//hw/bitstream/universal:rom",
        "@lowrisc_opentitan//hw/bitstream/universal:otp",
        "@lowrisc_opentitan//hw/bitstream/universal:env",
        "@lowrisc_opentitan//hw/top",
    ],
)
