# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
from collections import OrderedDict
from pathlib import Path
import hjson
import logging
import argparse

INDENT = "    "

DEFS_BZL_TEMPLATE = """
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip", "opentitan_top")

{topname} = {top}
"""


def indent_text(text, indent):
    return "".join(indent + line for line in text.splitlines(True))


class BazelRule:
    def __init__(self, rule_name, bzl_mapper = None):
        self.rule_name = rule_name
        self.args = OrderedDict()
        self.bzl_mapper = bzl_mapper

    def _stringify_arg(self, value):
        # Automatically map paths.
        if isinstance(value, Path) and self.bzl_mapper:
            value = self.bzl_mapper.map_file(value)
            # fallthrough
        # Automatically quote strings.
        if isinstance(value, str):
            value = f'"{value}"'
        elif isinstance(value, list):
            value = "[\n" + indent_text(
                ",\n".join(self._stringify_arg(x) for x in value), INDENT) + "\n]"
        else:
            value = str(value)
        return value

    def add_arg(self, name, value):
        value = self._stringify_arg(value)
        self.args[name] = value

    def __str__(self):
        text = ",\n".join([
            "{} = {}".format(name, value)
            for (name, value) in self.args.items()
        ])
        return "{}(\n{}\n)".format(self.rule_name, indent_text(text, INDENT))


class BazelMapper:
    def __init__(self, mapping):
        self.mapping = []
        for (bzl_path, fs_path) in mapping:
            if not bzl_path.endswith("//:BUILD.bazel"):
                logging.error(f"bazel mapping {bzl_path} does not refer to a BUILD.bazel" +
                              " file at the root of a repository")
                raise RuntimeError(f"invalid bazel mapping {bzl_path}")
            self.mapping.append(
                (Path(fs_path).resolve().parent,
                 bzl_path.removesuffix(":BUILD.bazel"))
            )

    def __str__(self):
        return "BazelMapper:\n" + "\n".join(f"- {fs_dir} -> {bzl_pkg}"
                                            for (fs_dir, bzl_pkg) in self.mapping)

    def map_file(self, f):
        fpath = f.resolve()
        # Find which, if any, of the repositories contains this file.
        for (fs_path, bzl_path) in self.mapping:
            if fpath.is_relative_to(fs_path):
                # We now need to figure out the bazel package to which this
                # file belongs. The best we can do is some guesswork: find the
                # closest BUILD.bazel in the hierarchy and hope that it exports
                # this file/target.
                pkg = None
                for parent in fpath.parents:
                    if any((parent / build).exists() for build in ["BUILD", "BUILD.bazel"]):
                        pkg = parent
                        break
                if pkg is None:
                    logging.warning(f"could not resolve bazel package for {fpath} " +
                                    f"relative to {fs_path}")
                    return fpath

                res = "{}{}:{}".format(
                    bzl_path,
                    pkg.relative_to(fs_path),
                    fpath.relative_to(pkg),
                )
                logging.debug(f"map {f} -> {res}")
                return res
        # If we cannot resolve it as a bazel path, we can always use an absolute path
        # but this may cause problems, depending on the use case.
        logging.warning(f"cannot map file {f} to any bazel location")
        return fpath


def resolve_ip_hjson(ip_name, ip_dirs):
    """
    Given an IP name and a list of directories, find the corresponding
    IP's Hjson, or return None.
    """
    for ip_dir in ip_dirs:
        ip_dir = ip_dir / ip_name
        if ip_dir.exists():
            logging.info(f"{ip_name} resolved to {ip_dir}")
            hjson = ip_dir / "data" / f"{ip_name}.hjson"
            if not hjson.exists():
                logging.error(f"{hjson} does not exist")
                return None
            return hjson
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'top_cfg',
        type = Path,
        help = "Path to a top hjson file",
    )
    parser.add_argument(
        '--map-bazel',
        action = 'append',
        default = [],
        nargs = 2,
        metavar = ("BZL_PATH", "FS_PATH"),
        help = """Specify a bazel mapping from a package label to a file system path.
Each assignment means that BZL_PATH corresponds to FS_PATH. Each BZL_PATH must
be refer to a BUILD.bazel file at the root of a repository, e.g. @lowrisc_opentitan//:BUILD.bazel.
The FS_PATH must be the corresponding path on the filesystem.
"""
    )
    parser.add_argument(
        "--ip-dir",
        action = 'append',
        type = Path,
        default = [],
        help = """Specify an IP directory. If several are specified, they will be search in the
order in which they appear on the command line."""
    )
    parser.add_argument(
        "-o",
        dest = "output",
        type = Path,
        help = "Output file name",
        required = True,
    )
    parser.add_argument(
        "--verbose", "-v",
        action = "count",
        default = 0,
        help = "Increase verbosity level",
    )
    args = parser.parse_args()
    if args.verbose >= 3:
        log_level = logging.DEBUG
    elif args.verbose == 2:
        log_level = logging.INFO
    elif args.verbose == 1:
        log_level = logging.WARNING
    else:
        log_level = logging.ERROR
    logging.basicConfig(level=log_level)

    bzl_mapper = BazelMapper(args.map_bazel)
    logging.info(bzl_mapper)

    top_cfg_path = args.top_cfg
    # Load top's Hjson file.
    if not top_cfg_path.exists():
        logging.error(f"{top_cfg_path} does not exist")
        return 1
    try:
        top_cfg = hjson.loads(top_cfg_path.read_text(), use_decimal=True)
    except Exception as e:
        logging.error(f"{top_cfg_path} cannot be loaded: ")
        logging.error(e)
    # Extract top's name.
    top_name = top_cfg["name"]

    logging.info(f"top is {top_name}")

    # Make sure that it is in the correct subdirectory.
    if top_cfg_path.parts[-2] != "autogen" or top_cfg_path.parts[-3] != "data":
        logging.error(f"{top_cfg_path} is not in the data/autogen subdirectory")
        return 1
    # Derive other artefacts from this.
    top_dir = top_cfg_path.parents[2]
    top_sw_autogen = top_dir / "sw" / "autogen"

    # Extract list of IP types.
    ips = []
    for ip_name in [m["type"] for m in top_cfg["module"]]:
        ip_hjson = resolve_ip_hjson(ip_name, args.ip_dir)
        if ip_hjson is None:
            logging.error(f"{top_cfg_path}: could not resolve IP {ip_name}")
            return 1

        ip_desc = BazelRule("opentitan_ip", bzl_mapper)
        ip_desc.add_arg("name", ip_name)
        ip_desc.add_arg("hjson", ip_hjson)
        ips.append(ip_desc)

    top_desc = BazelRule("opentitan_top", bzl_mapper)
    top_desc.add_arg("name", top_name)
    top_desc.add_arg("hjson", top_cfg_path)
    top_desc.add_arg("top_lib", top_sw_autogen / f"top_{top_name}")
    top_desc.add_arg("top_ld", top_sw_autogen / f"top_{top_name}_memory")
    top_desc.add_arg("ips", ips)

    top_desc_text = DEFS_BZL_TEMPLATE.format(
        topname = "TOP",
        top = str(top_desc)
    )
    try:
        args.output.write_text(top_desc_text)
    except Exception as e:
        logging.error("cannot write output file defs.bzl: ")
        logging.error(e)
    return 0


if __name__ == '__main__':
    sys.exit(main())
