#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""autogen_dif.py is a script for creating the automatic generated part
of the DIFs.
"""

import argparse
from pathlib import Path

from autogen_banner import get_autogen_banner
from make_new_dif.ip import Ip
from mako.template import Template
from mako import exceptions
from repo_top import repo_top

REPO_TOP = repo_top()


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--ipcfg",
        "-i",
        type=Path,
        required=True,
        help="`<ip>.hjson` file."
    )
    parser.add_argument(
        "--outdir",
        "-o",
        type=Path,
        required=True,
        help="Output directory"
    )

    args = parser.parse_args()

    if not args.outdir.is_dir():
        raise ValueError("{} is not a directory or does not exist".format(args.outdir))

    # Load IP.
    ip_name_snake = args.ipcfg.stem
    ip = Ip(ip_name_snake, "AUTOGEN", args.ipcfg)

    # Render DIF templates.
    template_path = REPO_TOP / "util/make_new_dif/templates"
    # Render all templates
    for filetype in [".h", ".c", "_unittest.cc"]:
        # Build input/output file names.
        template_file = template_path / f"dif_autogen{filetype}.tpl"
        out_file = (args.outdir /
                    f"dif_{ip.name_snake}_autogen{filetype}")

        # Read in template.
        try:
            template = Template(template_file.read_text(),
                                strict_undefined=True)
        except Exception as e:
            print(e)
            raise ValueError("unable to parse template {}".format(template_file))

        # Generate output file.
        try:
            out_text = template.render(
                ip=ip,
                autogen_banner=get_autogen_banner(
                    "util/autogen_dif.py -i {} -o {}".format(args.ipcfg, args.outdir),
                    "//"
                )
            )
        except:  # noqa: E722
            print(exceptions.text_error_template().render())
            raise ValueError("unable to render template {}".format(template_file))

        # Write output file.
        out_file.write_text(out_text)


if __name__ == "__main__":
    main()
