# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to describe OpenTitan HW"""

load("//rules:host.bzl", "host_tools_transition")

def opentitan_ip(name, **kwargs):
    """
    Return a structure describing an IP. This can be given to opentitan_top.

    Example:
    ```
    opentitan_ip(
        name = "pwrmgr",
        'hjson' = "//hw/top_earlgrey/ip_autogen/pwrmgr:data/pwrmgr.hjson",
        'ipconfig' = "//hw/top_earlgrey/ip_autogen/pwrmgr:data/top_earlgrey_pwrmgr.ipconfig.hjson",
    )
    ```

    Arguments:
    - name: name of ip in lower case.
    - kwargs: arbitrary IP attributes.
    """
    return struct(
        name = name,
        attrs = kwargs,
    )

def opentitan_top(name, ips, **kwargs):
    """
    Return a structure describing a top.

    Arguments:
    - name: name of top in lower case.
    - ips: array of ips, the entries must be built by opentitan_ip().
    - kwargs: arbitrary top attributes.
    """
    return struct(
        name = name,
        ips = ips,
        attrs = kwargs,
    )

def opentitan_modify_top(top, **kwargs):
    """
    Return a modified top.

    Supported modifications:
    - name: change the top name

    Arguments:
    - top: top created by opentitan_top
    - kwargs: arbitrary list of modifications
    """
    name = kwargs.pop("name", "")
    if kwargs:
        fail("unknown modifications:", kwargs)

    # Convert the struct to a dictionary.
    attrs = {
        key: getattr(top, key)
        for key in dir(top)
        if key != "to_json" and key != "to_proto"
    }

    # Apply modifications.
    if name:
        attrs["name"] = name

    # Re-create top.
    return struct(**attrs)

def has_top_attr(top, name):
    """
    Check whether a top has an attribute.

    Parameters:
    - top: top created by `opentitan_top`
    - name: name of the attribute
    """
    return name in top.attrs

def get_top_attr(top, name, required = True, default = None):
    """
    Given a top description, extract a top attribute.

    If `required` is set to `True`, this function will fail if the top
    does not have the requested attribute. Otherwise it will return `default`.

    Parameters:
    - top: top created by `opentitan_top`
    - name: name of the attribute
    - required: fail if the top does not have the attribute
    - default: this value will be returned when the top does not have this attribute
    """
    if has_top_attr(top, name):
        return top.attrs[name]
    else:
        if required:
            fail("top {} does not have attribute '{}'".format(top.name, name))
        return default

def has_ip(top, ipname):
    """
    Check whether a top has a particular IP.

    Parameters:
    - top: top created by `opentitan_top`
    - ipname: IP name
    """
    return any([ip.name == ipname for ip in top.ips])

def _get_ip(top, ipname, default = None):
    """
    Return the requested IP or a default value.

    Parameters:
    - top: top created by `opentitan_top`
    - ip: IP name
    """
    for ip in top.ips:
        if ip.name == ipname:
            return ip
    return default

def has_ip_attr(top, ipname, name):
    """
    Check whether a top's IP has an attribute. This function will return False if
    the top does not have the requested IP.

    Parameters:
    - top: top created by `opentitan_top`
    - ipname: IP name
    - name: name of the attribute
    """
    ip = _get_ip(top, ipname, None)
    return ip != None and name in ip.attrs

def get_ip_attr(top, ipname, name, required = True, default = None):
    """
    Given a top description, extract an IP's attribute.

    If `required` is set to `True`, this function will fail if the top
    does not have the requested IP, or if the IP does not have the requested
    attribute. Otherwise it will return `default`.

    Parameters:
    - top: top created by `opentitan_top`
    - ipname: IP name
    - name: name of the attribute
    - required: fail if the IP does not have the attribute
    - default: this value will be returned when the top does not have this IP or
               if the IP does not have this attribute
    """
    ip = _get_ip(top, ipname, None)
    if ip == None:
        if required:
            fail("top {} does not have IP {}".format(top.name, ipname))
        return default
    else:
        if required and name not in ip.attrs:
            fail("top {}, IP {} does not have attribute '{}'".format(top.name, ipname, name))
        return ip.attrs.get(name, default)
