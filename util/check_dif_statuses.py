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

# Maintain a list of IPs that only exist in the top-level area.
#
# Note that there are several templated IPs that are auto-generated in the
# top-level area as well, but since the bulk of the code (including the
# template) lives in the hw/ip area, we do not need to consider them.
_TOP_LEVEL_IPS = {"ast", "sensor_ctrl"}

# Indicates that the DIF work has not yet started.
_NOT_STARTED = colored("NOT STARTED", "red")

# This file is $REPO_TOP/util/make_new_dif/ip.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent


class _OTComponent(Enum):
    """Type of OpenTitan component."""
    DIF = 1
    HW = 2


class _DIFFunctionType(Enum):
    """Type of DIF function."""
    ALERT = 1
    IRQ = 2
    UNIMPLEMENTED = 3


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
    def __init__(self, top_level, difs_root_path, dif_name):
        """Mines metadata to populate this DIFStatus object.

        Args:
            top_level: Name of the top level design.
            difs_root_path: Path to DIF source code from REPO_TOP.
            dif_name: Full name of the DIF including the IP name.

        Raises:
            ValueError: Raised if DIF name does not start with "dif_".
        """
        # Get DIF/IP names and path.
        if not dif_name.startswith("dif_"):
            raise ValueError("DIF name should start with \"dif_\".")
        self.dif_name = dif_name
        self.ip = self.dif_name[4:]
        self.dif_path = os.path.join(difs_root_path, dif_name)

        # Check if header file exists - if not then its not even begun.
        has_started = os.path.isfile(self.dif_path + ".h")
        self.hw_path = (f"hw/{top_level}/ip/{self.ip}"
                        if self.ip in _TOP_LEVEL_IPS else f"hw/ip/{self.ip}")

        # Indicates DIF API completeness.
        self.num_functions_defined = -1
        self.num_functions_implemented = -1
        self.api_complete = False
        self.irq_funcs = set()
        self.alert_funcs = set()

        # Determine last date HW was updated.
        self.hw_last_modified = self._get_last_commit_date(
            os.path.join(self.hw_path, "rtl"), [""])

        # Determine the main contributor of the HW.
        self.hw_main_contributors = self._get_main_contributor_emails(
            _OTComponent.HW)
        if has_started:
            # Determine last date DIF was updated.
            self.dif_last_modified = self._get_last_commit_date(
                self.dif_path, [".h", ".c"])
            # Determine the main contributor of the DIF.
            self.dif_main_contributors = self._get_main_contributor_emails(
                _OTComponent.DIF)
            # Determine lifecycle state
            self.lifecycle_state = self._get_dif_lifecycle_state()
            # Determine DIF API completeness.
            self.funcs_unimplemented = self._get_funcs_unimplemented()
        else:
            self.dif_last_modified = "-"
            self.dif_main_contributors = [_NOT_STARTED]
            self.lifecycle_state = "-"
            self.funcs_unimplemented = [_NOT_STARTED]

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

    def _get_last_commit_date(self, file_path, exts):
        last_dif_commit_date = None
        for ext in exts:
            # Check the file exists.
            full_file_path = file_path + ext
            if os.path.isfile(full_file_path) or os.path.isdir(full_file_path):
                repo = pydriller.Repository(
                    str(REPO_TOP), filepath=full_file_path).traverse_commits()
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
        return last_dif_commit_date.strftime("%Y-%m-%d %H:%M:%S")

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
        defined_funcs = self._get_funcs(header_file)
        self.irq_funcs = self._get_irq_funcs_defined(defined_funcs)
        self.alert_funcs = self._get_alert_funcs_defined(defined_funcs)
        return defined_funcs

    def _get_implemented_funcs(self):
        c_file = self.dif_path + ".c"
        # If no .c file exists --> All functions are undefined.
        if not os.path.isfile(c_file):
            return set()
        return self._get_funcs(c_file)

    def _get_funcs(self, file_path):
        func_pattern = re.compile(r"^dif_result_t (dif_.*)\(.*")
        funcs = set()
        with open(file_path, "r") as fp:
            for line in fp:
                result = func_pattern.search(line)
                if result is not None:
                    funcs.add(result.group(1))
        return funcs

    def _get_expected_irqs(self):
        # TODO: parse HJSON to get expected IRQ info per IP
        logging.error(f"{self._get_expected_irqs.__name__}() unimplemented.")
        sys.exit(1)

    def _get_expected_alerts(self):
        # TODO: parse HJSON to get expected Alert info per IP
        logging.error(f"{self._get_expected_irqs.__name__}() unimplemented.")
        sys.exit(1)

    def _get_irq_funcs_defined(self, defined_funcs):
        assert defined_funcs and "Expected defined_funcs to be non-empty."
        irq_funcs = set()
        for func in defined_funcs:
            if "irq" in func:
                irq_funcs.add(func)
        return irq_funcs

    def _get_alert_funcs_defined(self, defined_funcs):
        assert defined_funcs and "Expected defined_funcs to be non-empty."
        alert_funcs = set()
        for func in defined_funcs:
            if "alert" in func:
                alert_funcs.add(func)
        return alert_funcs


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


def print_function_set(dif_statuses: List[DIFStatus],
                       dif_function_type: _DIFFunctionType,
                       table_format: str) -> None:
    """Print a table of specific functions names DIF functions to STDOUT.

    Args:
        dif_statuses: List of DIFStatus objects containing metadata about DIF
            development states.
        dif_function_type: DIFs to display in {ALERT, IRQ, UNIMPLEMENTED}
        table_format: Format of output table to print. See tabulate module.

    Returns:
        None
    """
    # Print label of function type.
    if dif_function_type == _DIFFunctionType.ALERT:
        print("Alert Functions:")
    elif dif_function_type == _DIFFunctionType.IRQ:
        print("IRQ Functions:")
    elif dif_function_type == _DIFFunctionType.UNIMPLEMENTED:
        print("Unimplemented Functions:")
    else:
        logging.error("Invalid function type to print table.")
        sys.exit(1)

    # Build and print table.
    rows = []
    headers = ["IP", "Function"]
    for dif_status in dif_statuses:
        if dif_function_type == _DIFFunctionType.ALERT:
            if dif_status.alert_funcs:
                rows.append([dif_status.ip, "\n".join(dif_status.alert_funcs)])
        elif dif_function_type == _DIFFunctionType.IRQ:
            if dif_status.irq_funcs:
                rows.append([dif_status.ip, "\n".join(dif_status.irq_funcs)])
        elif dif_function_type == _DIFFunctionType.UNIMPLEMENTED:
            if not dif_status.api_complete:
                rows.append(
                    [dif_status.ip, "\n".join(dif_status.funcs_unimplemented)])
        else:
            # Unreachable.
            logging.error("Invalid function type to print table.")
            sys.exit(1)
    print(tabulate(rows, headers, tablefmt=table_format))


def main(argv):
    # Process args and set logging level.
    # TODO: parallelize data scraping so its much faster
    parser = argparse.ArgumentParser(
        prog="check_dif_statuses",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--top-hjson",
        help="""Path to the top-level HJSON configuration file relative to
        REPO_TOP.""")
    parser.add_argument(
        "--show-unimplemented",
        action="store_true",
        help="""Show unimplemented functions for each incomplete DIF.""")
    parser.add_argument("--show-alerts",
                        action="store_true",
                        help="""Show alert functions for each DIF.""")
    parser.add_argument("--show-irqs",
                        action="store_true",
                        help="""Show IRQ functions for each DIF.""")
    parser.add_argument("--table-format",
                        type=str,
                        choices=["grid", "github", "pipe"],
                        default="grid",
                        help="""Format to print status tables in.""")
    args = parser.parse_args(argv)
    logging.basicConfig(level=logging.WARNING)

    # Define root path of DIFs.
    difs_root_path = os.path.join("sw", "device", "lib", "dif")

    if args.top_hjson:
        # Get the list of IP blocks by invoking the topgen tool.
        topgen_tool = os.path.join(REPO_TOP, "util", "topgen.py")
        top_hjson = os.path.join(REPO_TOP, args.top_hjson)
        top_level = Path(top_hjson).stem
        # yapf: disable
        topgen_process = subprocess.run([topgen_tool, "-t", top_hjson,
                                         "--get_blocks", "-o", REPO_TOP],
                                        text=True,
                                        universal_newlines=True,
                                        stdout=subprocess.PIPE,
                                        check=True)
        # yapf: enable
        # All DIF names are prefixed with `dif_`.
        difs = {f"dif_{dif.strip()}" for dif in topgen_process.stdout.split()}
    else:
        # Get list of all DIF basenames.
        # TODO: automatically get the list below by cross referencing DIF names
        # with IP block names. Hardcoded for now.
        print("WARNING: It is recommended to pass the --top-hjson switch to "
              "get a more accurate representation of the DIF progress. The "
              "list of IPs for which no DIF sources exist is unknown.")
        shared_headers = ["dif_base"]
        top_level = "top_earlgrey"
        difs = get_list_of_difs(difs_root_path, shared_headers)

    # Get DIF statuses (while displaying a progress bar).
    dif_statuses = []
    progress_bar = enlighten.Counter(total=len(difs),
                                     desc="Analyzing statuses of DIFs ...",
                                     unit="DIFs")
    for dif in difs:
        dif_statuses.append(DIFStatus(top_level, difs_root_path, dif))
        progress_bar.update()

    # Build table and print it to STDOUT.
    print_status_table(dif_statuses, args.table_format)
    if args.show_unimplemented:
        print_function_set(dif_statuses, _DIFFunctionType.UNIMPLEMENTED,
                           args.table_format)
    if args.show_alerts:
        print_function_set(dif_statuses, _DIFFunctionType.ALERT,
                           args.table_format)
    if args.show_irqs:
        print_function_set(dif_statuses, _DIFFunctionType.IRQ,
                           args.table_format)


if __name__ == "__main__":
    main(sys.argv[1:])
