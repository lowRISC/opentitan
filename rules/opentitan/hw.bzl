# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to describe OpenTitan HW"""

OpenTitanIpInfo = provider(
    doc = "Information about an OpenTitan IP block",
    fields = {
        "name": "Name of this IP block (string)",
        "hjson": "HJSON file for this IP block (file)",
    },
)

def _opentitan_ip_impl(ctx):
    return [
        OpenTitanIpInfo(
            name = ctx.label.name,
            hjson = ctx.file.hjson,
        ),
    ]

opentitan_ip = rule(
    implementation = _opentitan_ip_impl,
    doc =
        """
        Create a description of an OpenTitan IP that can be consumed by opentitan_top.
        This rule provides a OpenTitanIpInfo and the RTL files in the DefaultInfo.
        """,
    attrs = {
        "hjson": attr.label(allow_single_file = True, doc = "HJSON file that describes this IP block"),
    },
    provides = [OpenTitanIpInfo],
)

OpenTitanTopInfo = provider(
    doc = "Information about an OpenTitan top",
    fields = {
        "name": "Name of this top (string)",
        "hjson": "topgen-generated HJSON file for this top (file)",
        "ip_hjson": "dictionary of IPs HSJON files (dict: string => file)",
    },
)

def _opentitan_top_impl(ctx):
    ips = [ip[OpenTitanIpInfo] for ip in ctx.attr.ips]
    return [
        OpenTitanTopInfo(
            name = ctx.label.name,
            hjson = ctx.file.hjson,
            ip_hjson = {ip.name: ip.hjson for ip in ips},
        ),
    ]

opentitan_top = rule(
    implementation = _opentitan_top_impl,
    doc =
        """
        Create a description of an OpenTitan top that can be consumed by various rules.
        This rule provides a OpenTitanTopInfo and the RTL files in the DefaultInfo.
        """,
    attrs = {
        "hjson": attr.label(allow_single_file = True, doc = "topgen-generated HJSON file that describes this top"),
        "ips": attr.label_list(providers = [OpenTitanIpInfo], doc = "List of IPs used by this top"),
    },
    provides = [OpenTitanTopInfo],
)
