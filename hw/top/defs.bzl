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
    names = {}
    for top in ALL_TOPS:
        for ip in top.ips:
            names[ip.name] = {}
    return names.keys()

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
      name = "bla",
      target_compatible_with = opentitan_require_ip("uart"),
    )
    """
    return opentitan_if_ip(ip, [], ["@platforms//:incompatible"])

def opentitan_select_top(values, default):
    """
    Select a value based on the top. If not top matches, a default
    value is returned. The values must be a dictionary where each key
    is either a string, or an array of string.

    Example:
    alias(
      name = "bla",
      actual = opentitan_select_top({
        "earlgrey": "//something:earlgrey",
        ["english_breakfast", "darjeeling"]: "//something:else",
      }, "//something:error")
    )
    """
    branches = {}
    for (tops, value) in values.items():
        if type(tops) == "string":
            tops = [tops]
        for top in tops:
            branches["//hw/top:is_{}".format(top)] = value
    branches["//conditions:default"] = default
    return select(branches)

def opentitan_require_top(top):
    """
    Return a value that can be used with `target_compatible_with` to
    express that this target only works on the requested top.

    Example:
    cc_library(
      name = "bla",
      target_compatible_with = opentitan_require_ip("uart"),
    )
    """
    return opentitan_select_top({top: []}, ["@platforms//:incompatible"])
