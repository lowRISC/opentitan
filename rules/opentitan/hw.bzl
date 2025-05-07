# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to describe OpenTitan HW"""

load("//rules:host.bzl", "host_tools_transition")

def opentitan_ip(name, attrs = {}, **kwargs):
    """
    Return a structure describing an IP. This can be given to opentitan_top.

    Example:
    ```
    opentitan_ip(
        name = "pwrmgr",
        attrs = {
            'hjson': "//hw/top_earlgrey/ip_autogen/pwrmgr:data/pwrmgr.hjson",
            'ipconfig': "//hw/top_earlgrey/ip_autogen/pwrmgr:data/top_earlgrey_pwrmgr.ipconfig.hjson",
        },
    )
    ```

    Arguments:
    - name: name of ip in lower case.
    - attrs: a map from strings to labels, you MUST NOT use a relative label.
    - kwargs: for backward compatibility, any key listed here will be treated as a key in `attrs`
    """
    return struct(
        name = name,
        attrs = attrs | kwargs,
    )

def opentitan_top(name, ips, attrs = {}, **kwargs):
    """
    Return a structure describing a top.

    Arguments:
    - name: name of top in lower case.
    - ips: array of ips, the entries must be built by opentitan_ip().
    - attrs: a map from strings to labels, you MUST NOT use a relative label.
    - kwargs: for backward compatibility, any key listed here will be treated as a key in `attrs`.
    """
    return struct(
        name = name,
        attrs = attrs | kwargs,
        ips = ips,
    )

OpenTitanTopInfo = provider(
    doc = "Information about an OpenTitan top",
    fields = {
        "name": "Name of this top (string)",
        "attrs": "dictionary of top attrs (dict: {attr name (string)}: target",
        "ip_map": "dictionary of IPs attrs (dict: {ipname (string): {attr (string): target}})",
    },
)

def opentitan_top_get_ip_attr(
        top,
        ipname,
        attr,
        required = True,
        default = None,
        output = "file"):
    """
    Return an IP's attribute (e.g. 'hjson'). If `required` is set, this function will
    throw an error when the attribute is not present. Otherwise, it will return `default`.
    In all cases, the function will throw an error if the IP is not present in the top.

    Arguments:
    - top: an `OpenTitanTopInfo` provider.
    - ipname: name of the IP.
    - attr: name of the attribute.
    - required: whether the attribute is required.
    - output: specifies the output type (see below).
    - default: return value if `required` is false and the attribute is not present.

    The output type specifies what kind of processing is done on the target:
    - "files": will return the DefaultInfo as a list of files
    - "file": same as file but return a single file, error if there are more
    - "target": return the raw bazel target
    """
    if ipname not in top.ip_map:
        fail("top {} does not contain IP {}".format(top.name, ipname))
    ip_attrs = top.ip_map[ipname]
    if required and (attr not in ip_attrs):
        fail("top {} does not contain attribute '{}' for IP {}".format(top.name, attr, ipname))

    target = ip_attrs.get(attr, None)
    if target == None:
        return default
    if output in ["file", "files"]:
        files = target[DefaultInfo].files.to_list()
        if output == "file" and len(files) != 1:
            fail("IP {} in top {} provide several files for attribute {} but only one requested"
                .format(ipname, top.name, attr))

        return files[0] if output == "file" else files
    else:
        return target

def opentitan_top_get_attr(
        top,
        attr,
        required = True,
        default = None,
        output = "file"):
    """
    Return a top's attribute (e.g. 'hjson'). If `required` is set, this function will
    throw an error when the attribute is not present. Otherwise, it will return `default`.

    Arguments:
    - top: an `OpenTitanTopInfo` provider.
    - attr: name of the attribute.
    - required: whether the attribute is required.
    - output: specifies the output type (see below).
    - default: return value if `required` is false and the attribute is not present.

    The output type specifies what kind of processing is done on the target:
    - "files": will return the DefaultInfo as a list of files
    - "file": same as file but return a single file, error if there are more
    - "target": return the raw bazel target
    """
    if required and (attr not in top.attrs):
        fail("top {} does not contain attribute '{}'".format(top.name, attr))

    target = top.attrs.get(attr, None)
    if target == None:
        return default
    if output in ["file", "files"]:
        files = target[DefaultInfo].files.to_list()
        if output == "file" and len(files) != 1:
            fail("top {} provide several files for attribute {} but only one requested"
                .format(top.name, attr))

        return files[0] if output == "file" else files
    else:
        return target

def _describe_top(ctx):
    ip_map = {}

    # We cannot use ctx.attrs because it is only a list and not a dict.
    for (encoded, attrs) in ctx.attr.ip_map.items():
        ipname, attr = encoded.split("/", 1)

        if ipname not in ip_map:
            ip_map[ipname] = {}
        ip_map[ipname][attr] = attrs

    return [
        OpenTitanTopInfo(
            name = ctx.attr.topname,
            ip_map = ip_map,
            attrs = ctx.attr.attrs,
        ),
    ]

describe_top_rule = rule(
    implementation = _describe_top,
    doc = """Create a target that provides the description of a top in the form of an OpenTitanTopInfo provider.""",
    attrs = {
        "ip_map": attr.string_keyed_label_dict(
            allow_files = True,
            # Transition to host because some of those attributes could use targets (e.g. python libraries) that only work
            # on the host platform.
            cfg = host_tools_transition,
            doc = "mapping from '<ipname>/<attr>' to targets",
        ),
        "attrs": attr.string_keyed_label_dict(
            allow_files = True,
            doc = "mapping from '<attr>' to targets",
        ),
        "topname": attr.string(mandatory = True, doc = "Name of the top"),
    },
)

def describe_top(name, all_tops, top):
    """
    Create a target that provides an OpenTitanTopInfo corresponding to the
    requested top.

    - all_tops: list of tops (created by opentitan_top).
    - top: name of the top to use.
    """

    # Although we already pass the top description to the rule, those are just strings.
    # We also need to let bazel know that we depend on the files in `attrs` which is why
    # we also pass them in a structured way.
    ip_map = {}
    top_attrs = None
    for _top in all_tops:
        if _top.name != top:
            continue
        top_attrs = _top.attrs
        for ip in _top.ips:
            for (attr, value) in ip.attrs.items():
                ip_map["{}/{}".format(ip.name, attr)] = value

    describe_top_rule(
        name = name,
        attrs = top_attrs,
        ip_map = ip_map,
        topname = top,
    )



def select_top_lib(name, all_tops, top):
    """
    Create an alias to the top library.
    """
    libs = [_top.attrs["top_lib"] for _top in all_tops if _top.name == top]
    if len(libs) == 0:
        fail("not top found with name {}".format(top))

    native.alias(
        name = name,
        actual = libs[0],
    )

def select_top_ld(name, all_tops, top):
    """
    Create an alias to the top library.
    """
    libs = [_top.attrs["top_ld"] for _top in all_tops if _top.name == top]
    if len(libs) == 0:
        fail("not top found with name {}".format(top))

    native.alias(
        name = name,
        actual = libs[0],
    )
