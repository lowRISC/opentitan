# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "get_ip_attr", "get_top_attr", "has_ip_attr", "has_top_attr")
load("@tops_desc//:defs.bzl", _ALL_TOPS = "ALL_TOPS")

ALL_TOPS = _ALL_TOPS

ALL_TOP_NAMES = [
    top.name
    for top in ALL_TOPS
]

def _all_ip_names():
    names = {ip.name: 1 for top in ALL_TOPS for ip in top.ips}
    return sorted(names.keys())

ALL_IP_NAMES = _all_ip_names()

def _all_seed_names():
    names = {}
    for top in ALL_TOPS:
        names.update(top.attrs.get("secret_cfgs", {}))
    return sorted(names.keys())

ALL_SEED_NAMES = _all_seed_names()

def opentitan_if_ip(ip, obj, default):
    """
    Return a select expression that evaluate to `obj` if the ip is
    supported by the active top, and `default` otherwose.

    Example:
    ```python
    # Optional dependency on the usbdev with a define.
    cc_library(
      name = "my_library",
      defines = opentitan_if_ip("usbdev", ["HAS_USBDEV"], []),
      deps = opentitan_if_ip("usbdev", ["@lowrisc_opentitan//sw/device/lib/dif:usbdev"], []),
    )
    ```
    """
    compatible_tops = []
    for top in ALL_TOPS:
        for _ip in top.ips:
            if _ip.name == ip:
                compatible_tops.append(top.name)
                break

    return select({
        "@lowrisc_opentitan//hw/top:is_{}".format(top): obj
        for top in compatible_tops
    } | {
        "@lowrisc_opentitan//conditions:default": default,
    })

def opentitan_require_ip(ip):
    """
    Return a value that can be used with `target_compatible_with` to
    express that this target only works on top with the requested IP.

    Example:
    ```python
    cc_library(
      name = "my_library",
      target_compatible_with = opentitan_require_ip("uart"),
    )
    ```
    """
    return opentitan_if_ip(ip, [], ["@platforms//:incompatible"])

def opentitan_select_top(values, default):
    """
    Select a value based on the top. If no top matches, a default
    value is returned. The values must be a dictionary where each key
    is either a string, or an array of string.

    Example:
    ```python
    alias(
      name = "my_alias",
      actual = opentitan_select_top({
        "earlgrey": "@lowrisc_opentitan//something:earlgrey",
        ("englishbreakfast", "darjeeling"): "@lowrisc_opentitan//something:else",
      }, "@lowrisc_opentitan//something:error")
    )
    ```
    """
    branches = {}
    for (tops, value) in values.items():
        if type(tops) == "string":
            tops = [tops]
        for top in tops:
            branches["@lowrisc_opentitan//hw/top:is_{}".format(top)] = value
    branches["@lowrisc_opentitan//conditions:default"] = default
    return select(branches)

def opentitan_require_top(top):
    """
    Return a value that can be used with `target_compatible_with` to
    express that this target only works on the requested top.
    The argument can either be a string ("earlgrey") or a list of strings
    (["earlgrey", "darjeeling"]).

    Example:
    ```python
    cc_library(
      name = "my_library",
      target_compatible_with = opentitan_require_top("darjeeling"),
    )
    ```
    """
    return opentitan_select_top({top: []}, ["@platforms//:incompatible"])

def opentitan_select_top_attr(attr_name, required = True, default = None, fn = None):
    """
    Return a select expression that gives access to a chosen top attribute. Specifically,
    `fn` will be called for each top that has this attribute and the returned value will be
    inserted into the select expression. `fn` defaults to the identity function if not
    provided, returning the attribute itself.

    If `required` is set to `True`, the selection expression will only contain branches
    for tops containing the attribute and an error message will be set in case there is no match.
    Therefore informally the select will look like:
    ```py
    select({
      <if top A>: fn(<top A attribute>),
      <if top B>: fn(<top B attribute>),
      .. and so on for all tops with the given attribute ..
    }, no_match_error = "this top does not have the requested attribute")
    ```

    If `required` is set to `False`, the selection expression will contain a default branch
    whole value is set to `default`.
    Therefore informally the select will look like:
    ```py
    select({
      <if top A>: fn(<top A attribute>),
      <if top B>: fn(<top B attribute>),
      .. and so on for all tops with the given attribute ..
      <default>: default
    })
    ```
    """

    def maybe_fn(x):
        return fn(x) if fn != None else x

    branches = {
        "@lowrisc_opentitan//hw/top:is_{}".format(top.name): maybe_fn(get_top_attr(top, attr_name))
        for top in ALL_TOPS
        if has_top_attr(top, attr_name)
    }
    if not required:
        branches["@lowrisc_opentitan//conditions:default"] = default
        no_match_error = ""
    else:
        no_match_error = "the select top does not have attribute '{}'".format(attr_name)
    return select(branches, no_match_error = no_match_error)

def opentitan_if_top_attr(attr_name, obj, default):
    """
    Return a select expression evaluating to `obj` if the top has the requested attribute
    and to `default` if it does not. Informally, this expression looks like:
    ```py
    select({
      <if top has attribute>: obj,
      <default>: default,
    })
    ```
    """
    return opentitan_select_top_attr(attr_name, fn = lambda x: obj, required = False, default = default)

def opentitan_require_top_attr(attr_name):
    """
    Return a select expression which can be used together with `target_compatible_with`
    to express the requirement that the top must have the required attribute.
    """
    return opentitan_if_top_attr(attr_name, [], ["@platforms//:incompatible"])

def opentitan_alias_top_attr(name, attr_name, required = True, default = None, fn = None):
    """
    Create an alias to a top specific top attribute.  `fn` will be called for each top that
    has this attribute and the returned value will be interpreted as a label string.
    `fn` defaults to the identity function if not provided, returning the attribute itself.

    If `required` is set to `True`, the alias will be marked as compatible only with tops
    containing the requested attribute.

    If `required` is set to `False`, the alias will point to `default` for tops which do
    not contain the requested attribute.
    """

    def maybe_fn(x):
        return fn(x) if fn != None else x

    native.alias(
        name = name,
        actual = opentitan_select_top_attr(attr_name, required, default, fn),
        target_compatible_with = opentitan_require_top_attr(attr_name) if required else [],
    )

def opentitan_select_ip_attr(ipname, attr_name, required = True, default = None, fn = None):
    """
    Return a select expression that gives access to a chosen IP attribute. Specifically,
    `fn` will be called for each top that has this IP's attribute and the returned value will be
    inserted into the select expression. `fn` defaults to the identity function if not
    provided, returning the attribute itself.

    If `required` is set to `True`, the selection expression will only contain branches
    for tops containing the (IP and the) IP attribute and an error message will be set in
    case there is no match.

    If `required` is set to `False`, the selection expression will contain a default branch
    whole value is set to `default`.
    """

    def maybe_fn(x):
        return fn(x) if fn != None else x

    branches = {
        "@lowrisc_opentitan//hw/top:is_{}".format(top.name): maybe_fn(get_ip_attr(top, ipname, attr_name))
        for top in ALL_TOPS
        if has_ip_attr(top, ipname, attr_name)
    }
    if not required:
        branches["@lowrisc_opentitan//conditions:default"] = default
        no_match_error = ""
    else:
        no_match_error = "the select top does not have IP {} or its IP does not have attribute '{}'".format(ipname, attr_name)
    return select(branches, no_match_error = no_match_error)

def opentitan_if_ip_attr(ipname, attr_name, obj, default):
    """
    Return a select expression evaluating to `obj` if the top has the requested IP and
    the IP has the requested attribute, and to `default` if it does not.
    """
    return opentitan_select_ip_attr(ipname, attr_name, fn = lambda x: obj, required = False, default = default)

def opentitan_require_ip_attr(ipname, attr_name):
    """
    Return a select expression which can be used together with `target_compatible_with`
    to express the requirement that the top must have the required IP and the IP has
    the required attribute.
    """
    return opentitan_if_ip_attr(ipname, attr_name, [], ["@platforms//:incompatible"])
