# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:util.bzl", "flatten")
load("//hw/top:defs.bzl", "ALL_IP_NAMES", "opentitan_if_ip")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")
load("//rules:autogen.bzl", "opentitan_autogen_isr_testutils")

package(default_visibility = ["//visibility:public"])

opentitan_autogen_isr_testutils(
    name = "isr_testutils",
    target_compatible_with = [OPENTITAN_CPU],
    top = "//hw/top:top_desc",
    deps = [
               "//hw/top:top_lib",
               "//sw/device/lib/dif:rv_plic",
               "//sw/device/lib/testing/test_framework:check",
           ] + flatten([
               opentitan_if_ip(
                   ip,
                   ["//sw/device/lib/dif/autogen:{}".format(ip)],
                   [],
               )
               for ip in ALL_IP_NAMES
           ]) +
           # There is a special dependency for the adc_ctrl, see testutils template.
           opentitan_if_ip(
               "adc_ctrl",
               ["//sw/device/lib/dif:adc_ctrl"],
               [],
           ),
)
