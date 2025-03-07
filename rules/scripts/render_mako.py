#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
Render a mako template for the mako_template() rule.
"""

import sys
import argparse
from pathlib import Path
from mako.template import Template
from mako import exceptions


def render_template(template_path: Path, rendered_path: Path,
                    **other_info):

    tpl = Template(filename=str(template_path), strict_undefined = True)
    try:
        template_contents = tpl.render(**other_info)
    except:  # noqa: E722
        print(exceptions.text_error_template().render())
        return 1

    rendered_path.parent.mkdir(exist_ok=True, parents=True)
    with rendered_path.open(mode="w", encoding="UTF-8") as fout:
        fout.write(template_contents)

    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-o',
        action='store',
        required=True,
        dest='output',
        type=Path,
        help="output file",
    )
    parser.add_argument(
        'template',
        action='store',
        type=Path,
        help='Mako template to render')
    parser.add_argument(
        '--variable',
        action='append',
        default=[],
        metavar="VAR=VALUE",
        help="global variables for the template",
    )
    args = parser.parse_args()

    variables = {}
    for varstr in args.variable:
        var, sep, val = varstr.partition("=")
        assert sep == "=", "invalid variable: the format must be VAR=VALUE"
        variables[var] = val

    return render_template(args.template, args.output, **variables)


if __name__ == '__main__':
    sys.exit(main())
