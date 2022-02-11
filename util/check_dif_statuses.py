#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""DIF Status Report Generator.

This tool generates a status report for the DIFs by cross referencing the git
commit history of each DIF with that of the HW it actuates to provide OpenTitan
developers with information about what DIFs require updating.

To display usage run:
    ./check_dif_statuses.py --help
"""

import argparse
import collections
import io
import itertools
import json
import logging
import re
import subprocess
import sys
from contextlib import redirect_stdout
from enum import Enum
from pathlib import Path
from typing import List

import enlighten
import gitfame
import hjson
import pydriller
from tabulate import tabulate
from termcolor import colored

import topgen.lib as lib

# Maintain a list of IPs that only exist in the top-level area.
#
# Note that there are several templated IPs that are auto-generated in the
# top-level area as well, but since the bulk of the code (including the
# template) lives in the hw/ip area, we do not need to consider them.
# These IPs are slowly being migrated to use the `ipgen` tooling, and are
# defined in the IPS_USING_IPGEN list in the make_new_dif.ip module imported
# above.
_TOP_LEVEL_IPS = {"ast", "sensor_ctrl"}

# Indicates that the DIF work has not yet started.
_NOT_STARTED = colored("NOT STARTED", "red")

# This file is $REPO_TOP/util/check_dif_statuses.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent

# Define the DIF library relative to REPO_TOP.
DIFS_RELATIVE_PATH = Path("sw/device/lib/dif")


class _OTComponent(Enum):
    """Type of OpenTitan component."""
    DIF = 1
    HW = 2


class DIFStatus:
    """Holds all DIF status information for displaying.

    Attributes:
        dif_name (str): Full name of the DIF including the IP name.
        ip (str): Name of the IP the DIF is associated with.
        dif_path (Path): Path to the DIF code (relative to REPO_TOP).
        hw_path (Path): Path to the HW RTL associated with this DIF.
        dif_last_modified (datetime): Date and time the DIF was last modified.
        hw_last_modified (datetime): Date and time the HW was last modified.
        dif_main_contributors (List[str]): List of emails of DIF contributors.
        hw_main_constributors (List[str]): List of emails of HW contributors.
        lifecycle_state (str): Lifecycle state string (e.g., S0, S1, ...).
        num_functions_defined (int): Number of API functions defined.
        num_functions_implemented (int): Number of API functions implemented.
        api_complete (bool): Indicates if DIF implements all defined functions.
        funcs_unimplemented (Set[str]): Set of unimplemted DIF functions.

    """
    def __init__(self, ipgen_ips, top_level, dif_name):
        """Mines metadata to populate this DIFStatus object.

        Args:
            ipgen_ips: List of IPs generated with the ipgen.py tool.
            top_level: Name of the top level design.
            dif_name: Full name of the DIF including the IP name.

        Raises:
            ValueError: Raised if DIF name does not start with "dif_".
        """
        # Get DIF/IP names and path.
        if not dif_name.startswith("dif_"):
            raise ValueError("DIF name should start with \"dif_\".")
        self.dif_name = dif_name
        self.ip = self.dif_name[4:]
        self.dif_path = DIFS_RELATIVE_PATH / dif_name
        self.dif_autogen_path = (DIFS_RELATIVE_PATH /
                                 f"autogen/{dif_name}_autogen")

        # Check if header file exists - if not then its not even begun.
        has_started = self.dif_path.with_suffix(".h").is_file()

        # Get (relative) HW RTL path.
        if self.ip in ipgen_ips:
            self.hw_path = Path(f"hw/{top_level}/ip_autogen/{self.ip}")
        elif self.ip in _TOP_LEVEL_IPS:
            self.hw_path = Path(f"hw/{top_level}/ip/{self.ip}")
        else:
            self.hw_path = Path(f"hw/ip/{self.ip}")

        # Indicates DIF API completeness.
        self.num_functions_defined = -1
        self.num_functions_implemented = -1
        self.api_complete = False

        # Determine last date HW was updated.
        self.hw_last_modified = self._get_last_commit_date(
            [self.hw_path / "rtl"], [""])

        # Determine the main contributor of the HW.
        self.hw_main_contributors = self._get_main_contributor_emails(
            _OTComponent.HW)
        if has_started:
            # Determine last date DIF was updated.
            self.dif_last_modified = self._get_last_commit_date(
                [self.dif_path, self.dif_autogen_path], [".h", ".c"])
            # Determine the main contributor of the DIF.
            self.dif_main_contributors = self._get_main_contributor_emails(
                _OTComponent.DIF)
            # Determine lifecycle state
            self.lifecycle_state = self._get_dif_lifecycle_state()
            # Determine DIF API completeness.
            self.funcs_unimplemented = self._get_funcs_unimplemented()
        else:
            # Set DIF status data to indicate it has not started.
            self.dif_last_modified = "-"
            self.dif_main_contributors = [_NOT_STARTED]
            self.lifecycle_state = "-"
            self.funcs_unimplemented = [_NOT_STARTED]

    def _get_dif_lifecycle_state(self):
        hjson_filename = self.hw_path / f"data/{self.ip}.prj.hjson"
        with open(hjson_filename, "r") as life_f:
            lifecycle_data = hjson.load(life_f)
        # If there are multiple revisions, grab the latest.
        if "revisions" in lifecycle_data:
            lifecycle_data = lifecycle_data["revisions"][-1]
        if "dif_stage" in lifecycle_data:
            return lifecycle_data["dif_stage"]
        return "-"

    def _get_main_contributor_emails(self, component):
        # Get contributor stats for HW or DIF (SW) and sort by LOC.
        if component == _OTComponent.DIF:
            stats = self._get_contributors(
                [self.dif_path, self.dif_autogen_path], [".h", ".c"])
        else:
            stats = self._get_contributors([self.hw_path / "rtl"], [""])
        sorted_stats = sorted(stats.items(), key=lambda x: x[1], reverse=True)
        # If the second contributor has contributed at least 10% as much as the
        # first contributor, include both second and first contributors.
        contributor_1_email, contributor_1_loc = sorted_stats[0]
        if len(sorted_stats) > 1:
            contributor_2_email, contributor_2_loc = sorted_stats[1]
            if (float(contributor_2_loc) / float(contributor_1_loc)) > 0.1:
                return [contributor_1_email, contributor_2_email]
        return [contributor_1_email]

    def _get_contributors(self, file_paths, exts):
        contributor_stats = collections.defaultdict(int)
        for file_path, ext in itertools.product(file_paths, exts):
            full_file_path = file_path.with_suffix(ext)
            output = io.StringIO()
            try:
                # Use gitfame to fetch commit stats, captured from STDOUT.
                with redirect_stdout(output):
                    gitfame.main(args=[
                        f"--incl={full_file_path}", "-s", "-e", "--log=ERROR",
                        "--format=json"
                    ])
            except FileNotFoundError:
                logging.error(f"(contributors) file path ({full_file_path}) "
                              "does not exist.")
                sys.exit(1)
            gitfame_commit_stats = json.loads(output.getvalue())
            for contributor_stat in gitfame_commit_stats["data"]:
                contributor = contributor_stat[0]
                loc = contributor_stat[1]
                if loc == 0:
                    break
                contributor_stats[contributor] += loc
        return contributor_stats

    def _get_last_commit_date(self, file_paths, exts):
        last_dif_commit_date = None
        for file_path, ext in itertools.product(file_paths, exts):
            full_file_path = file_path.with_suffix(ext)
            try:
                repo = pydriller.Repository(
                    str(REPO_TOP), filepath=full_file_path).traverse_commits()
            except FileNotFoundError:
                logging.error(
                    f"(date) file path ({full_file_path}) does not exist.")
                sys.exit(1)
            for commit in repo:
                if last_dif_commit_date is None:
                    last_dif_commit_date = commit.author_date
                else:
                    last_dif_commit_date = max(last_dif_commit_date,
                                               commit.author_date)
        return last_dif_commit_date.strftime("%Y-%m-%d %H:%M:%S")

    def _get_funcs_unimplemented(self):
        defined_funcs = self._get_defined_funcs()
        implemented_funcs = self._get_implemented_funcs()
        self.num_functions_defined = len(defined_funcs)
        self.num_functions_implemented = len(implemented_funcs)
        self.api_complete = bool(defined_funcs and
                                 defined_funcs == implemented_funcs)
        if len(defined_funcs) < len(implemented_funcs):
            logging.warning(
                f"number of defined functions is less than implemented "
                f"functions for {self.ip}. Results possibly invalid.")
            print("Functions missing definitions:")
            for impl_func in implemented_funcs:
                if impl_func not in defined_funcs:
                    print(f"\t{impl_func}")
        return defined_funcs - implemented_funcs

    def _get_defined_funcs(self):
        header_file = self.dif_path.with_suffix(".h")
        autogen_header_file = self.dif_autogen_path.with_suffix(".h")
        defined_funcs = self._get_funcs(header_file)
        defined_funcs |= self._get_funcs(autogen_header_file)
        return defined_funcs

    def _get_implemented_funcs(self):
        c_file = self.dif_path.with_suffix(".c")
        c_autogen_file = self.dif_autogen_path.with_suffix(".c")
        # The autogenerated header should always exist if the DIF has been
        # started.
        implemented_funcs = self._get_funcs(c_autogen_file)
        # However, the manually-implemented header may not exist yet.
        # If no .c file exists --> All functions are undefined.
        if c_file.is_file():
            implemented_funcs |= self._get_funcs(c_file)
        return implemented_funcs

    def _get_funcs(self, file_path):
        func_pattern = re.compile(r"dif_result_t (dif_.*)\(.*")
        funcs = set()
        with open(file_path, "r") as fp:
            for line in fp:
                result = func_pattern.search(line)
                if result is not None and not line.startswith("static"):
                    funcs.add(result.group(1))
        return funcs


def print_status_table(dif_statuses: List[DIFStatus],
                       table_format: str) -> None:
    """Print a table of DIF status information to STDOUT.

    Args:
        dif_statuses: List of DIFStatus objects containing metadata about DIF
            development states.

    Returns:
        None
    """
    # Build the table.
    rows = []
    headers = [
        "IP", "DIF Updated", "HW Updated", "DIF Contributor*",
        "HW Contributor*", "Functions\nDefined", "Functions\nImplemented",
        "Stage"
    ]
    for dif_status in dif_statuses:
        # Color code last modified dates.
        # Limit the last modified strings to 10 characters to only print the
        # date (YYYY-MM-DD).
        hw_last_modified = dif_status.hw_last_modified[:10]
        dif_last_modified = dif_status.dif_last_modified[:10]
        if dif_status.hw_last_modified > dif_status.dif_last_modified:
            hw_last_modified = colored(hw_last_modified, "yellow")
            dif_last_modified = colored(dif_last_modified, "yellow")
        # Color code API complete status.
        if dif_status.api_complete:
            num_funcs_defined = colored(dif_status.num_functions_defined,
                                        "green")
            num_funcs_implemented = colored(
                dif_status.num_functions_implemented, "green")
        else:
            num_funcs_defined = colored(dif_status.num_functions_defined,
                                        "red")
            num_funcs_implemented = colored(
                dif_status.num_functions_implemented, "red")

        # Add row to table (printing one contributor email per line).
        rows.append([
            dif_status.ip, dif_last_modified, hw_last_modified,
            "\n".join(dif_status.dif_main_contributors),
            "\n".join(dif_status.hw_main_contributors), num_funcs_defined,
            num_funcs_implemented, dif_status.lifecycle_state
        ])

    # Print the table and legend.
    print("DIF Statuses:")
    print(tabulate(rows, headers, tablefmt=table_format))
    print("""*Only the top two contributors (by LOC) """
          """for each component are listed.""")
    print(colored("Yellow", "yellow"),
          "\t= HW has been updated since the DIF.")
    print(
        colored("Green", "green"),
        """\t= DIF API, as defined in the current header file, is complete. """
        """Note, the header file may lack necessary API functionality.""")
    print(colored("Red", "red"),
          ("\t= DIF API is incomplete, as defined in the header file or the "
           "work has not yet begun."))


def print_unimplemented_difs(dif_statuses: List[DIFStatus],
                             table_format: str) -> None:
    """Print a table of specific functions names DIF functions to STDOUT.

    Args:
        dif_statuses: List of DIFStatus objects containing metadata about DIF
            development states.
        table_format: Format of output table to print. See tabulate module.

    Returns:
        None
    """
    # Build and print table.
    print("Unimplemented Functions:")
    rows = []
    headers = ["IP", "Function"]
    for dif_status in dif_statuses:
        if not dif_status.api_complete:
            rows.append(
                [dif_status.ip, "\n".join(dif_status.funcs_unimplemented)])
    print(tabulate(rows, headers, tablefmt=table_format))


def main(argv):
    # Process args and set logging level.
    # TODO: parallelize data scraping so its much faster
    parser = argparse.ArgumentParser(
        prog="check_dif_statuses",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--show-unimplemented",
        action="store_true",
        help="""Show unimplemented functions for each incomplete DIF.""")
    parser.add_argument("--table-format",
                        type=str,
                        choices=["grid", "github", "pipe"],
                        default="grid",
                        help="""Format to print status tables in.""")
    parser.add_argument(
        "top_hjson",
        help="""Path to the top-level HJSON configuration file relative to
        REPO_TOP.""")
    args = parser.parse_args(argv)
    logging.basicConfig(level=logging.WARNING)

    # Make sure to call this script from REPO_TOP.
    if Path.cwd() != REPO_TOP:
        logging.error(f"Must call script from \"$REPO_TOP\": {REPO_TOP}")
        sys.exit(1)

    # Get the list of IP blocks by invoking the topgen tool.
    topgen_tool = REPO_TOP / "util/topgen.py"
    top_hjson = REPO_TOP / args.top_hjson
    top_level = top_hjson.stem
    top_hjson_text = top_hjson.read_text()
    topcfg = hjson.loads(top_hjson_text, use_decimal=True)
    ipgen_ips = lib.get_ipgen_modules(topcfg)
    # yapf: disable
    topgen_process = subprocess.run([topgen_tool, "-t", top_hjson,
                                     "--get_blocks", "-o", REPO_TOP],
                                    universal_newlines=True,
                                    stdout=subprocess.PIPE,
                                    check=True)
    # yapf: enable
    # All DIF names are prefixed with `dif_`.
    difs = {f"dif_{dif.strip()}" for dif in topgen_process.stdout.split()}

    # Get DIF statuses (while displaying a progress bar).
    dif_statuses = []
    progress_bar = enlighten.Counter(total=len(difs),
                                     desc="Analyzing statuses of DIFs ...",
                                     unit="DIFs")
    for dif in difs:
        dif_statuses.append(DIFStatus(ipgen_ips, top_level, dif))
        progress_bar.update()
    dif_statuses.sort(key=lambda x: x.ip)

    # Build table and print it to STDOUT.
    print_status_table(dif_statuses, args.table_format)
    if args.show_unimplemented:
        print_unimplemented_difs(dif_statuses, args.table_format)


if __name__ == "__main__":
    main(sys.argv[1:])
