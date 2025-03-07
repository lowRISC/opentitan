# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@local_config_platform//:constraints.bzl", "HOST_CONSTRAINTS")

def get_host_cpu():
    cpu_constraint = "@platforms//cpu:"
    for constraint in HOST_CONSTRAINTS:
        if constraint.startswith(cpu_constraint):
            return constraint[len(cpu_constraint):]
