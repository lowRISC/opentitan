#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Run the tests we're interested in, then file the results away.
"""

import argparse
import datetime
import sys
import os
import json

import gspread

import bazel_report
import push_google


def date_or_datetime(s):
    """
    Parse a date or a datetime into a datetime structure.
    """
    try:
        # Simple date and time
        dt = datetime.datetime.strptime(s, "%Y-%m-%d")
        dt.replace(hour=12, minute=0, second=0)
    except ValueError:
        # Fully specified date and time
        dt = datetime.datetime.strptime(s, "%Y-%m-%d %H:%M")
    return dt


parser = argparse.ArgumentParser(
    description="Importing test results from OpenTitan test runs"
)

parser.add_argument(
    "--results-date",
    type=date_or_datetime,
    default=None,
    help="Results data collection date",
)

parser.add_argument(
    "--parse",
    action="store_true",
    help="Collate output into a single JUnitXML file specified by --filename",
)

parser.add_argument(
    "--upload-sheet",
    action="store_true",
    help="Upload the result in --filename to google sheets.",
)

parser.add_argument(
    "--filename",
    type=str,
    default=None,
    required=True,
    help="Collate output into a single JUnitXML file",
)

parser.add_argument(
    "--output-flattened",
    action="store_true",
    default=False,
    help="Flatten the JUnitXML output to a single test suite (rather than multiple)",
)

parser.add_argument(
    "--output-add-hostname",
    action="store_true",
    default=False,
    help="Add the hostname to the test suites",
)

parser.add_argument(
    "--output-add-property",
    action="append",
    help="Add properties to the test suite in the form KEY=VALUE. May be specified "
    "multiple times",
)

parser.add_argument(
    "--runner-id", type=str, default="", help="A string identifying the board"
)

options = parser.parse_args()

# Get the path to the home directory
home_dir = os.path.expanduser("~")
config_filepath = os.path.join(home_dir, ".config/silicon-nightly-runner/config.json")
config = {}
with open(config_filepath, "r", encoding="utf-8") as f:
    config = json.load(f)

if options.parse:
    otdir = bazel_report.OTDir(
        config.get("ot_home") + "/bazel-out/", collection_date=options.results_date
    )
    if not otdir.ntests:
        sys.exit("No tests were found in {}".format(options.results_dir))

    properties = dict(prop.split("=", 1) for prop in options.output_add_property)
    otdir.write(
        options.filename,
        flatten_testsuites=options.output_flattened,
        add_hostname=options.output_add_hostname,
        add_properties=properties,
    )

if options.upload_sheet:
    if config.get("google_service_file"):
        gcreds = gspread.service_account(filename=config.get("google_service_file"))
    elif config.get("google_oauth_file"):
        gcreds = gspread.oauth(credentials_filename=config.get("google_oauth_file"))
    else:
        sys.exit(
            """Either google-oauth-file or google-service-file must be supplied in the
             config.json file."""
        )

    for sheet_id in config.get("sheet_id"):
        tab_name = config.get("sheet_tab")
        if options.runner_id:
            tab_name += " " + options.runner_id

        pusher = push_google.TestResultPusher(
            gcreds,
            sheet_id=sheet_id,
            sheet_tab=tab_name,
            row_offset=config.get("sheet_row_offset"),
            column_offset=config.get("sheet_column_offset"),
            test_name_column=config.get("sheet_testname_column_offset"),
        )
        pusher.push(options.filename)
