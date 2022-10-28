#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import pathlib3x as pathlib
from mako.template import Template

from metadata import LockedMetadata, RegressionMetadata
from ibex_cmd import get_config


def render_template(config_name: str, template_filename: str) -> str:
    ibex_config_template = Template(filename=template_filename)
    ibex_config = get_config(config_name)
    return ibex_config_template.render(ibex_config=ibex_config.params)


def _main():
    """Renders a mako template providing parameters from the metadata ibex
    config
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('template_filename')
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()

    with LockedMetadata(args.dir_metadata, __file__) as md:
        print(render_template(md.ibex_config, args.template_filename))


if __name__ == "__main__":
    _main()
