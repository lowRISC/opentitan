#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Command-line tool to generate devicetables file."""

import argparse
import logging
import hjson
from mako.template import Template
from mako import exceptions
from pathlib import Path

from reggen.ip_block import IpBlock
from dtgen.helper import TopHelper, IpHelper
from topgen.lib import CArrayMapping, CEnum

TOPGEN_TEMPLATE_PATH = Path(__file__).parents[1].resolve() / "util" / "dtgen"


def render_template(template_path: Path, rendered_path: Path,
                    **other_info):

    top_tpl = Template(filename=str(template_path))
    try:
        template_contents = top_tpl.render(**other_info)
    except:  # noqa: E722
        print(exceptions.text_error_template().render())
        raise ValueError("unable to render template {}".format(template_path))

    rendered_path.parent.mkdir(exist_ok=True, parents=True)
    with rendered_path.open(mode="w", encoding="UTF-8") as fout:
        fout.write(template_contents)


def main():
    logging.basicConfig(format="%(levelname)s: %(message)s", level=logging.WARNING)

    parser = argparse.ArgumentParser(prog="dtgen")
    parser.add_argument(
        "--topgencfg",
        "-t",
        type=Path,
        required=True,
        help="`top_{name}.gen.hjson` file."
    )
    parser.add_argument(
        "--ip",
        "-i",
        type=Path,
        action='append',
        default = [],
        help="IP hjson file, can be specified multiple times"
    )
    parser.add_argument(
        "--outdir",
        "-o",
        type=Path,
        required=True,
        help="Output directory"
    )
    parser.add_argument(
        "--gen-top",
        action='store_true',
        help="Generate top-level files (dt_api.h and devicetables.c/h)"
    )
    parser.add_argument(
        "--gen-ip",
        action='store_true',
        help="Generate IP-level files (dt_<ip>.h)"
    )
    parser.add_argument(
        "--default-node",
        action='store',
        default = None,
        help="Specify the default register block node (for --gen-ip)"
    )

    args = parser.parse_args()
    outdir = Path(args.outdir) / "dt"
    outdir.mkdir(parents = True, exist_ok = True)

    name_to_block = {}
    for ip_path in args.ip:
        ip = IpBlock.from_path(ip_path, [])
        name_to_block[ip.name.lower()] = ip

    with open(args.topgencfg) as handle:
        topcfg = hjson.load(handle, use_decimal=True)

    top_helper = TopHelper(topcfg, CEnum, CArrayMapping)

    if args.gen_top:
        top_lib_header = "hw/top_{0}/sw/autogen/top_{0}.h".format(topcfg["name"])

        render_template(
            TOPGEN_TEMPLATE_PATH / "dt_api.h.tpl",
            outdir / "dt_api.h",
            helper = top_helper,
            top_lib_header = top_lib_header,
        )
        render_template(
            TOPGEN_TEMPLATE_PATH / "dt_api.c.tpl",
            outdir / "dt_api.c",
            helper = top_helper,
        )

    if args.gen_ip:
        for (ipname, ip) in name_to_block.items():
            default_node = args.default_node
            if default_node is None:
                # Pick the first one.
                default_node = list(ip.reg_blocks.keys())[0]
                if len(ip.reg_blocks) > 1:
                    logging.warning(f"IP {ipname} has more than one register block node " +
                                    f"but no default was specified, will use {default_node}")

            helper = IpHelper(top_helper, ip, default_node, CEnum, CArrayMapping)

            render_template(
                TOPGEN_TEMPLATE_PATH / "dt_ip.h.tpl",
                outdir / "dt_{}.h".format(ipname),
                default_node = default_node,
                helper = helper,
            )
            render_template(
                TOPGEN_TEMPLATE_PATH / "dt_ip.c.tpl",
                outdir / "dt_{}.c".format(ipname),
                default_node = default_node,
                helper = helper,
            )


if __name__ == "__main__":
    main()
