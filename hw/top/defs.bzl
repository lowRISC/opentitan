# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_top")
load("//hw/top_earlgrey/data/autogen:defs.bzl", "EARLGREY")
load("//hw/top_darjeeling/data/autogen:defs.bzl", "DARJEELING")

ALL_TOPS = [
    EARLGREY,
    DARJEELING,
]

ALL_TOP_NAMES = [
    top.name
    for top in ALL_TOPS
]

def _all_ip_names():
    names = {ip.name: 1 for top in ALL_TOPS for ip in top.ips}
    return sorted(names.keys())

ALL_IP_NAMES = _all_ip_names()

def opentitan_if_ip(ip, obj, default):
    """
    Return a select expression that evaluate to `obj` if the ip is
    supported by the active top, and `default` otherwose.
    """
    compatible_tops = []
    for top in ALL_TOPS:
        for _ip in top.ips:
            if _ip.name == ip:
                compatible_tops.append(top.name)
                break

    return select({
        "//hw/top:is_{}".format(top): obj
        for top in compatible_tops
    } | {
        "//conditions:default": default,
    })

def opentitan_require_ip(ip):
    """
    Return a value that can be used with `target_compatible_with` to
    express that this target only works on top with the requested IP.

    Example:
    cc_library(
      name = "my_library",
      target_compatible_with = opentitan_require_ip("uart"),
    )
    """
    return opentitan_if_ip(ip, [], ["@platforms//:incompatible"])
