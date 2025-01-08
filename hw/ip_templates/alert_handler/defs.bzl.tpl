# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

${module_instance_name.upper()} = opentitan_ip(
    name = "${module_instance_name}",
    hjson = "//hw/top_${topname}/ip_autogen/${module_instance_name}:data/${module_instance_name}.hjson",
)
