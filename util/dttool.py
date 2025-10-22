#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Command-line tool to generate devicetables file."""

import argparse
import logging
import hjson
import inspect
from mako.template import Template
from mako import exceptions
from pathlib import Path
from importlib.util import module_from_spec, spec_from_file_location

from reggen.ip_block import IpBlock
from dtgen.helper import TopHelper, IpHelper, Extension
from dtgen.ipgen_ext import IpgenExt
from topgen.lib import CArrayMapping, CEnum

TOPGEN_TEMPLATE_PATH = Path(__file__).parents[1].resolve() / "util" / "dtgen"


def load_extension(plugin_path: Path):
    """Load an extension from a file."""
    if not plugin_path.exists():
        logging.error(f"Plugin file not found: {plugin_path}")
        return None

    spec = spec_from_file_location(name="dt_ext", location=plugin_path)

    if spec is None:
        logging.error(f"Module spec could not be loaded from {plugin_path}")
        return None

    if spec.loader is None:
        logging.error(f"Module spec does not have a loader for {plugin_path}")
        return None

    module = module_from_spec(spec)
    spec.loader.exec_module(module)

    return module


def find_extension_class(ext_mod, cls):
    if ext_mod is None:
        return []

    # Look for a class extended `cls`
    ext_cls = []
    for (name, obj) in inspect.getmembers(ext_mod):
        if not inspect.isclass(obj):
            continue
        # Only consider classes defined in this module.
        if obj.__module__ != ext_mod.__name__:
            continue
        if not issubclass(obj, cls):
            continue
        # Found one.
        ext_cls.append(obj)

    if not ext_cls:
        logging.error("extension does not define any extension class")
        raise RuntimeError("invalid extension")

    return ext_cls


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
    logging.basicConfig(format="%(filename)s:%(lineno)d: %(levelname)s: %(message)s",
                        level=logging.WARNING)

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
        "--ipconfig",
        type=Path,
        action='append',
        default = [],
        help="IP config hjson file, can be specified multiple times"
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
    parser.add_argument(
        "--extension",
        type=Path,
        help="Path to a DT extension (a python file)",
    )

    args = parser.parse_args()
    outdir = Path(args.outdir) / "dt"
    outdir.mkdir(parents = True, exist_ok = True)

    name_to_block = {}
    for ip_path in args.ip:
        ip = IpBlock.from_path(ip_path, [])
        name_to_block[ip.name.lower()] = ip
    name_to_ipconfig = {}
    for ipcfg_path in args.ipconfig:
        ipcfg = hjson.loads(ipcfg_path.read_text(), use_decimal=True)
        name_to_ipconfig[ipcfg["instance_name"]] = ipcfg

    with open(args.topgencfg) as handle:
        topcfg = hjson.load(handle, use_decimal=True)

    if args.extension:
        ext_mod = load_extension(args.extension)
        if ext_mod is None:
            raise RuntimeError("Could not load extension")
    else:
        ext_mod = None

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
                if len(ip.reg_blocks) == 0:
                    default_node = None
                else:
                    # Pick the first one.
                    default_node = list(ip.reg_blocks.keys())[0]
                if len(ip.reg_blocks) > 1:
                    logging.warning(f"IP {ipname} has more than one register block node " +
                                    f"but no default was specified, will use {default_node}")

            extension_cls = find_extension_class(ext_mod, Extension)
            extension_cls.append(IpgenExt)

            # The instance name is 'top_{topname}_{ipname}'.
            ipconfig = name_to_ipconfig.get('top_{}_{}'.format(topcfg["name"], ipname), None)

            helper = IpHelper(top_helper, ip, ipconfig, default_node, CEnum, CArrayMapping,
                              extension_cls)

            render_template(
                TOPGEN_TEMPLATE_PATH / "dt_ip.h.tpl",
                outdir / "dt_{}.h".format(ipname),
                helper = helper,
            )
            render_template(
                TOPGEN_TEMPLATE_PATH / "dt_ip.c.tpl",
                outdir / "dt_{}.c".format(ipname),
                helper = helper,
            )


if __name__ == "__main__":
    main()
