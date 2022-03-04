#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""IP Generator: Produce IP blocks from IP templates
"""
import argparse
import logging
import sys
from pathlib import Path

from ipgen import (IpBlockRenderer, IpConfig, IpTemplate, TemplateParseError,
                   TemplateRenderError)


def init_logging(verbose: bool) -> None:
    """ Initialize the logging system """
    if verbose:
        logging.basicConfig(format="%(levelname)s: %(message)s",
                            level=logging.DEBUG)
    else:
        logging.basicConfig(format="%(levelname)s: %(message)s")


def action_generate(ip_template: IpTemplate, args: argparse.Namespace) -> None:
    """ Handle the 'generate' action/subcommand. """
    overwrite_output_dir = args.force
    output_path = args.outdir

    # Read the IP configuration file.
    config_fp = args.config_file
    config_text = config_fp.read()
    config_fp.close()
    ip_config = IpConfig.from_text(ip_template.params,
                                   config_text, "the file passed to --config")

    # Render the IP template into an IP block.
    renderer = IpBlockRenderer(ip_template, ip_config)
    renderer.render(output_path, overwrite_output_dir)

    print(f"Wrote IP block {ip_config.instance_name!r} "
          f"from template {ip_template.name!r} to '{output_path}'.")


def action_describe(ip_template: IpTemplate, args: argparse.Namespace) -> None:
    """ Handle the 'describe' action/subcommand. """
    headline = f"IP template {ip_template.name!r}"
    print(headline)
    print('=' * len(headline))
    print()
    print(f"The template is stored in '{ip_template.template_path}'.")
    print()
    print("Template parameters")
    print("-------------------")
    print()
    for param in ip_template.params.values():
        print(f"{param.name}:")
        print(f"  Description: {param.desc}")
        print(f"  Type: {param.param_type}")
        print(f"  Default value: {param.default}")
        print()


def main() -> int:
    parser = argparse.ArgumentParser()

    # Shared arguments across all actions
    parent_parser = argparse.ArgumentParser(add_help=False)
    parent_parser.add_argument(
        "--verbose",
        help="More info messages",
        action="store_true",
    )
    parent_parser.add_argument(
        '-C',
        '--template-dir',
        type=Path,
        required=True,
        help='IP template directory',
    )

    subparsers = parser.add_subparsers(
        metavar='ACTION',
        title="actions",
        description=("Use 'ipgen.py ACTION --help' to learn more about the "
                     "individual actions."))
    subparsers.required = True

    # 'describe' subparser
    parser_generate = subparsers.add_parser(
        "describe",
        description="Show all information available for the IP template.",
        help="Show details about an IP template",
        parents=[parent_parser],
    )
    parser_generate.set_defaults(func=action_describe)

    # 'generate' subparser
    parser_generate = subparsers.add_parser(
        "generate",
        description="Generate an IP block from an IP template",
        help="Generate an IP block from an IP template",
        parents=[parent_parser],
    )
    parser_generate.add_argument(
        "-o",
        "--outdir",
        required=True,
        type=Path,
        help="output directory for the resulting IP block",
    )
    parser_generate.add_argument(
        "--force",
        "-f",
        required=False,
        default=False,
        action="store_true",
        help="overwrite the output directory, if it exists",
    )
    parser_generate.add_argument(
        "--config-file",
        "-c",
        required=True,
        type=argparse.FileType('r'),
        help="path to a configuration file",
    )
    parser_generate.set_defaults(func=action_generate)

    # Parse command line arguments, parse IP template, and invoke subparsers
    args = parser.parse_args()
    init_logging(args.verbose)

    try:
        ip_template = IpTemplate.from_template_path(args.template_dir)
        args.func(ip_template, args)
    except (TemplateParseError, TemplateRenderError) as e:
        if args.verbose:
            # Show the full backtrace if operating in verbose mode.
            logging.exception(e)
        else:
            # Otherwise just log the problem itself in a more user-friendly way.
            logging.error(str(e))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
