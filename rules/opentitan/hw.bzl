# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to describe OpenTitan HW"""

OpenTitanIpInfo = provider(
    doc = "Information about an OpenTitan IP block",
    fields = {
        "name": "Name of this IP block (string)",
        "hjson": "HJSON file for this IP block (file)",
        "rtl": "RTL files (depset)",
        "doc": "documentation files (depset)",
    },
)

def _opentitan_ip_impl(ctx):
    return [
        DefaultInfo(
            files = depset(ctx.files.rtl),
        ),
        OpenTitanIpInfo(
            name = ctx.label.name,
            hjson = ctx.file.hjson,
            rtl = depset(ctx.files.rtl),
            doc = depset(ctx.files.doc),
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
        "rtl": attr.label_list(allow_files = True, doc = "List of RTL files (core, verilog, ...) for this block"),
        "doc": attr.label_list(allow_files = True, doc = "List of files used to create the documentation of this block"),
    },
    provides = [OpenTitanIpInfo],
)

OpenTitanTopInfo = provider(
    doc = "Information about an OpenTitan top",
    fields = {
        "name": "Name of this top (string)",
        "hjson": "topgen-generated HJSON file for this top (file)",
        "ip_hjson": "dictionary of IPs HSJON files (dict: string => file)",
        "rtl": "all RTL files (depset)",
        "doc": "all documentation files (depset)",
    },
)

def _opentitan_top_impl(ctx):
    ips = [ip[OpenTitanIpInfo] for ip in ctx.attr.ips]
    rtl = depset(
        ctx.files.rtl,
        transitive = [ip.rtl for ip in ips],
    )
    doc = depset(
        ctx.files.doc,
        transitive = [ip.doc for ip in ips],
    )
    return [
        DefaultInfo(
            files = rtl,
        ),
        OpenTitanTopInfo(
            name = ctx.label.name,
            hjson = ctx.file.hjson,
            rtl = rtl,
            doc = doc,
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
        "rtl": attr.label_list(allow_files = True, doc = "List of RTL files (core, verilog, ...) for this top"),
        "doc": attr.label_list(allow_files = True, doc = "List of files used to create the documentation of this top"),
        "ips": attr.label_list(providers = [OpenTitanIpInfo], doc = "List of IPs used by this top"),
    },
    provides = [OpenTitanTopInfo],
)
