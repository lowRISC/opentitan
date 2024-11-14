#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Command-line tool to generate devicetables file."""

import argparse
import logging
import hjson
import sys
from mako.template import Template
from pathlib import Path

from reggen.ip_block import IpBlock

TOPGEN_TEMPLATE_PATH = Path(__file__).parents[1].resolve() / "util" / "dtgen"


def render_template(template_path: Path, rendered_path: Path,
                    **other_info):

    top_tpl = Template(filename=str(template_path))
    template_contents = top_tpl.render(**other_info)

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
    outdir = Path(args.outdir)

    name_to_block = {}
    for ip_path in args.ip:
        ip = IpBlock.from_path(ip_path, [])
        name_to_block[ip.name.lower()] = ip

    topcfg = None
    if args.topgencfg is not None:
        with open(args.topgencfg) as handle:
            topcfg = hjson.load(handle, use_decimal=True)

    if args.gen_top:
        if topcfg is None:
            logging.error("--gen-top requires --topgencfg to be specified")
            sys.exit(1)

        module_types = {m["type"] for m in topcfg["module"]}
        dt_headers = []
        for m in module_types:
            dt_headers.append(f"dt_{m}.h")
            if m not in name_to_block:
                logging.error("IP block {} required by top but not specified using -i".format(m))
                sys.exit(1)

        render_template(
            TOPGEN_TEMPLATE_PATH / "dt_api.h.tpl",
            outdir / "dt_api.h",
            top=topcfg,
            name_to_block = name_to_block
        )

        render_template(
            TOPGEN_TEMPLATE_PATH / "devicetables.c.tpl",
            outdir / "devicetables.c",
            top=topcfg,
            name_to_block = name_to_block
        )

        render_template(
            TOPGEN_TEMPLATE_PATH / "devicetables.h.tpl",
            outdir / "devicetables.h",
            top=topcfg,
            name_to_block = name_to_block,
            dt_headers = dt_headers
        )

    if args.gen_ip:
        for (ipname, ip) in name_to_block.items():
            default_node = args.default_node
            if default_node is None:
                # Pick the first one.
                default_node = list(ip.reg_blocks.keys())[0]
                if len(ip.reg_blocks) > 1:
                    logging.warning(f"IP {ipname} has more than one register block node but " +
                                    f"no default was specified, will use {default_node}")
                else:
                    # If there is a single node, it may not have a name, in which case
                    # the template will call it 'core'.
                    if default_node is None:
                        default_node = "core"

            render_template(
                TOPGEN_TEMPLATE_PATH / "dt_ip.h.tpl",
                outdir / "dt_{}.h".format(ipname),
                block = ip,
                default_node = default_node,
            )


if __name__ == "__main__":
    main()
