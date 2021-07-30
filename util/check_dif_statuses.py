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
import glob
import io
import json
import logging
import os
import re
import sys
from contextlib import redirect_stdout
from enum import Enum
from typing import List

import enlighten
import gitfame
import hjson
import pydriller
from tabulate import tabulate
from termcolor import colored

# The IP suffix of some DIFs are slightly different than the IP directory name
# in the hw/ip/ directory, so here is the translation for the applicable IPs.
IP_TRANSLATION = {
    "plic": "rv_plic",
    "entropy": "entropy_src",
}


class _OTComponent(Enum):
    """Type of OpenTitan component."""
    DIF = 1
    HW = 2


class DIFStatus:
    """Holds all DIF status information for displaying.

    Attributes:
        dif_name (str): Full name of the DIF including the IP name.
        ip (str): Name of the IP the DIF is associated with.
        dif_path (str): Path to the DIF code.
        hw_path (str): Path to the HW RTL associated with this DIF.
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
    def __init__(self, repo_top, difs_root_path, dif_name):
        """Mines metadata to populate this DIFStatus object.

        Args:
            repo_top: Relative path of local OpenTitan repository.
            difs_root_path: Path to DIF source code from repo_top.
            dif_name: Full name of the DIF including the IP name.

        Raises:
            ValueError: Raised if DIF name does not start with "dif_".
        """
        # Get DIF/IP names and path.
        if not dif_name.startswith("dif_"):
            raise ValueError("DIF name should start with \"dif_\".")
        self.dif_name = dif_name
        self.ip = self.dif_name[4:]
        if self.ip in IP_TRANSLATION:
            self.ip = IP_TRANSLATION[self.ip]
        self.dif_path = os.path.join(difs_root_path, dif_name)
        self.hw_path = f"hw/ip/{self.ip}"
        # Determine last date DIF and HW was updated.
        self.dif_last_modified = self._get_last_commit_date(
            repo_top, self.dif_path, [".h", ".c"])
        self.hw_last_modified = self._get_last_commit_date(
            repo_top, os.path.join(self.hw_path, "rtl"), [""])
        # Determine the main contributor of the DIF and HW.
        self.dif_main_contributors = self._get_main_contributor_emails(
            _OTComponent.DIF)
        self.hw_main_contributors = self._get_main_contributor_emails(
            _OTComponent.HW)
        # Determine lifecycle state
        self.lifecycle_state = self._get_dif_lifecycle_state()
        # Determine DIF API completeness.
        self.num_functions_defined = -1
        self.num_functions_implemented = -1
        self.api_complete = False
        self.funcs_unimplemented = self._get_funcs_unimplemented()

    def _get_dif_lifecycle_state(self):
        hjson_filename = os.path.join(self.hw_path, "data",
                                      self.ip + ".prj.hjson")
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
            stats = self._get_contributors(self.dif_path, [".h", ".c"])
        else:
            stats = self._get_contributors(os.path.join(self.hw_path, "rtl"),
                                           ["/*"])
        sorted_stats = sorted(stats.items(), key=lambda x: x[1], reverse=True)
        # If the second contributor has contributed at least 10% as much as the
        # first contributor, include both second and first contributors.
        contributor_1_email, contributor_1_loc = sorted_stats[0]
        if len(sorted_stats) > 1:
            contributor_2_email, contributor_2_loc = sorted_stats[1]
            if (float(contributor_2_loc) / float(contributor_1_loc)) > 0.1:
                return [contributor_1_email, contributor_2_email]
        return [contributor_1_email]

    def _get_contributors(self, file_path, exts):
        contributor_stats = collections.defaultdict(int)
        for ext in exts:
            # Check the file/path exists.
            full_file_path = file_path + ext
            if os.path.isfile(full_file_path) or (
                    full_file_path.endswith("*") and
                    os.path.isdir(full_file_path[:-2])):
                # Use gitfame to fetch commit stats, captured from STDOUT.
                output = io.StringIO()
                with redirect_stdout(output):
                    gitfame.main(args=[
                        f"--incl={full_file_path}", "-s", "-e", "--log=ERROR",
                        "--format=json"
                    ])
                gitfame_commit_stats = json.loads(output.getvalue())
                for contributor_stat in gitfame_commit_stats["data"]:
                    contributor = contributor_stat[0]
                    loc = contributor_stat[1]
                    if loc == 0:
                        break
                    contributor_stats[contributor] += loc
            else:
                logging.error(
                    f"""(contributors) file path ({full_file_path}) """
                    """does not exist.""")
                sys.exit(1)
        return contributor_stats

    def _get_last_commit_date(self, repo_top, file_path, exts):
        last_dif_commit_date = None
        for ext in exts:
            # Check the file exists.
            full_file_path = file_path + ext
            if os.path.isfile(full_file_path) or os.path.isdir(full_file_path):
                repo = pydriller.Repository(
                    repo_top, filepath=full_file_path).traverse_commits()
                for commit in repo:
                    if last_dif_commit_date is None:
                        last_dif_commit_date = commit.author_date
                    else:
                        last_dif_commit_date = max(last_dif_commit_date,
                                                   commit.author_date)
            else:
                logging.error(
                    f"(date) file path ({full_file_path}) does not exist.")
                sys.exit(1)
        return last_dif_commit_date

    def _get_funcs_unimplemented(self):
        defined_funcs = self._get_defined_funcs()
        implemented_funcs = self._get_implemented_funcs()
        self.num_functions_defined = len(defined_funcs)
        self.num_functions_implemented = len(implemented_funcs)
        self.api_complete = bool(defined_funcs and
                                 defined_funcs == implemented_funcs)
        return defined_funcs - implemented_funcs

    def _get_defined_funcs(self):
        header_file = self.dif_path + ".h"
        return self._get_funcs(header_file)

    def _get_implemented_funcs(self):
        c_file = self.dif_path + ".c"
        # If no .c file exists --> All functions are undefined.
        if not os.path.isfile(c_file):
            return set()
        return self._get_funcs(c_file)

    def _get_funcs(self, file_path):
        func_pattern = re.compile(r"^dif_.*_result_t (dif_.*)\(.*")
        funcs = set()
        with open(file_path, "r") as fp:
            for line in fp:
                result = func_pattern.search(line)
                if result is not None:
                    funcs.add(result.group(1))
        return funcs


def get_list_of_difs(difs_root_path: str, shared_headers: List[str]) -> None:
    """Get a list of the root filenames of the DIFs.

    Args:
        difs_root_path: Root path where DIF source files are located.
        shared_headers: Header file(s) shared amongst DIFs.

    Returns:
        None
    """
    dif_headers = list(glob.glob(os.path.join(difs_root_path, "*.h")))
    dif_headers = map(os.path.basename, dif_headers)
    difs = set(map(lambda s: s.split(".")[0], dif_headers))
    for header in shared_headers:
        if header in difs:
            difs.remove(header)
    return difs


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
        if dif_status.hw_last_modified > dif_status.dif_last_modified:
            hw_last_modified = colored(dif_status.hw_last_modified.date(),
                                       "yellow")
            dif_last_modified = colored(dif_status.dif_last_modified.date(),
                                        "yellow")
        else:
            hw_last_modified = dif_status.hw_last_modified.date()
            dif_last_modified = dif_status.dif_last_modified.date()
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
          "\t= DIF API is incomplete, as defined in the header file.")


def print_unimplemented_functions(dif_statuses: List[DIFStatus],
                                  table_format: str) -> None:
    """Print a table of unimplemented DIF functions to STDOUT.

    Args:
        dif_statuses: List of DIFStatus objects containing metadata about DIF
            development states.

    Returns:
        None
    """
    rows = []
    headers = ["IP", "Function"]
    for dif_status in dif_statuses:
        if not dif_status.api_complete:
            rows.append(
                [dif_status.ip, "\n".join(dif_status.funcs_unimplemented)])
    print("Unimplemented Functions:")
    print(tabulate(rows, headers, tablefmt=table_format))


def main(argv):
    # Process args.
    parser = argparse.ArgumentParser(
        prog="check_dif_statuses",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "repo_top",
        help=
        """Relative path to where the OpenTitan repository is checked out.""")
    parser.add_argument(
        "--show-unimplemented",
        action="store_true",
        help="""Show unimplemented functions for each incomplete DIF.""")
    parser.add_argument("--table-format",
                        type=str,
                        choices=["grid", "github", "pipe"],
                        default="grid",
                        help="""Format to print status tables in.""")
    args = parser.parse_args(argv)

    # Define root path of DIFs.
    difs_root_path = os.path.join("sw", "device", "lib", "dif")

    # Get list of all DIF basenames.
    # TODO: automatically get the list below by cross referencing DIF names
    # with IP block names. Hardcoded for now.
    shared_headers = ["dif_warn_unused_result"]
    difs = get_list_of_difs(difs_root_path, shared_headers)

    # Get DIF statuses (while displaying a progress bar).
    dif_statuses = []
    progress_bar = enlighten.Counter(total=len(difs),
                                     desc="Analyzing statuses of DIFs ...",
                                     unit="DIFs")
    for dif in difs:
        dif_statuses.append(DIFStatus(args.repo_top, difs_root_path, dif))
        progress_bar.update()

    # Build table and print it to STDOUT.
    print_status_table(dif_statuses, args.table_format)
    if args.show_unimplemented:
        print_unimplemented_functions(dif_statuses, args.table_format)


if __name__ == "__main__":
    main(sys.argv[1:])
