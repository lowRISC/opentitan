#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate SVD file from top and module hjson files.
"""

import argparse
import hjson
import itertools
import pathlib
import sys

import reggen
import svdgen
import topgen

from logging import info, warning, fatal

def load_top_hjson(path: pathlib.Path) -> hjson:
    """Load a top-level chip definition from an HJSON file. Basic sanity
    checks on the system are performed."""

    with path.open('r') as f:
        top = hjson.load(f, use_decimal=True)

    return top

def load_ip_hjson(path: pathlib.Path) -> hjson:
    """Load an IP module's register definition from an HJSON file. This
    validates the file, and ensures the module's name is in a compatible
    capitalization with the top-level configuration (some modules define
    UPPERCASE_NAMES, while the top config expects lowercase)."""

    with path.open('r') as f:
        ip = hjson.load(f, use_decimal=True,
             object_pairs_hook=reggen.validate.checking_dict)
        if reggen.validate.validate(ip) != 0:
            raise SystemExit('failed to validate %s' % ip.stem)

    name = ip['name'].lower()
    ip['name'] = name

    return name, ip


def main():
    parser = argparse.ArgumentParser(prog='svdtool')
    parser.add_argument('--topcfg', required=True,
        default='hw/top_earlgrey/data/top_earlgrey.hjson',
        help='the top .hjson configuration file (')
    parser.add_argument('--ip-dir', required=True,
        default='hw/ip',
        help='the directory containing the peripheral .hjson files')
    parser.add_argument('--filter-ip', action='append',
        default=['rv_plic', 'pinmux'],
        help='ignore peripheral .hjson and use top level instead')
    parser.add_argument('--set-version',
        help='''the version string to embed in the <cpu> field
        (read from `git describe` if left unspecified)''')

    args = parser.parse_args()
    version = args.set_version or svdgen.read_git_version()

    # exclude rv_plic (to use top_earlgrey one) and
    ips = topgen.search_ips(pathlib.Path(args.ip_dir))
    #ips = [ip for ip in ips if not ip.parents[1].name in args.filter_ip]

    top_hjson = load_top_hjson(pathlib.Path(args.topcfg))
    ips_hjson = dict(load_ip_hjson(ip) for ip in ips)

    if list(map(fatal, svdgen.validate(top_hjson, ips_hjson))):
        raise SystemExit('invalid top and/or register HJSON')

    copyright = map(lambda l: l[2:-1],
        itertools.takewhile(lambda l: l.startswith('# '),
        itertools.dropwhile(lambda l: l.startswith('#!'),
        open(__file__))))

    device = svdgen.generate(top_hjson, ips_hjson, version)
    svdgen.write_to_file(device, copyright, sys.stdout)

if __name__ == '__main__':
    main()
