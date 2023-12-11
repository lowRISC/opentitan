#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script parses the dv testplan and generates a csv or/and update a spreadsheet.

usage with a single file:
    ./util/py/scripts/testplan_decoder.py --file <path/to/hjson/file> \
    --csv <path/to/output/csv>

usage with a dir:
    ./util/py/scripts/testplan_decoder.py --dir <path/to/dir/with/hjson/files> \
    --csv <path/to/output/csv>
"""

import argparse
import glob
import json
import logging
import os
import re
import sys
from enum import Enum

import hjson
import pandas as pd
from gh_issues_manager import GithubWrapper
from mako.template import Template

parser = argparse.ArgumentParser()
parser.add_argument(
    "--logging",
    default="info",
    choices=["debug", "info", "warning", "error", "critical"],
    help="Logging level",
)

parser.add_argument("--file",
                    required=False,
                    help="Path of a single testplan hjson file.")
parser.add_argument("--dir",
                    required=False,
                    help="Path of a dir containing the testplan files.")

# Create subparsers for each subcommand
subparsers = parser.add_subparsers(title='subcommands',
                                   dest='command',
                                   help='subcommand help')

# Subparser for the 'export' command
export_parser = subparsers.add_parser(
    'export',
    help=
    'Export the testplan in different formats [csv, google sheet, github issues] '
)
export_parser.add_argument(
    "--csv",
    default="./tests.csv",
    help="Path of the output csv file.",
)
export_parser.add_argument(
    "--url",
    help="url of a google sheet.",
)
export_parser.add_argument(
    "--credentials",
    help="""Path to a json file with the google credentials.
          Check https://docs.gspread.org/en/latest/oauth2.html for more details.""",
)
export_parser.add_argument(
    "--github-token",
    help="""Token""",
)
export_parser.add_argument(
    "--issue-template",
    help="""Template""",
)
export_parser.add_argument(
    "--bazel-suite",
    help="""Output the bazel test suite as an output""",
)

# Subparser for the 'update' command
update_parser = subparsers.add_parser(
    'update', help='Update the testplans based on a csv')
update_parser.add_argument(
    "--csv",
    required=True,
    help="Path of the input csv file.",
)


def main(args):
    if args.dir is None and args.file is None:
        print("The input must be specified by either using --file or --dir")

    files = [args.file] if args.file else []
    if args.dir:
        files += [f for f in glob.glob(f"{args.dir}/*.hjson")]

    df = None
    for file in files:
        df = pd.concat([df, dataframe_from_testplan(file)])

    if args.command == 'export':
        return export_cmd(args, df)
    elif args.command == 'update':
        return update_cmd(args)

    return -1


LICENSE_HEADER = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
"""


def update_cmd(args):
    files = [f for f in glob.glob(f"{args.dir}/*.hjson")]

    df = pd.read_csv(args.csv).fillna("None")
    df.groupby("hw_ip_block").apply(
        lambda block: update_ip_block(files, block))


def update_ip_block(files, block_dataframe):
    ip_name = block_dataframe.iloc[0]["hw_ip_block"]

    filename = get_testplan_filename(ip_name, files)
    if filename:
        testplan = hjson.load(open(filename, "r"))
        updated = block_dataframe.apply(
            lambda row: update_testpoint(testplan, row), axis=1)
        if any(updated):  #Update if there was a change.
            logging.info(f"Updating {filename}.")
            with open(filename, "w") as f:
                f.write(LICENSE_HEADER)
                hjson.dump(testplan, f, indent=2, for_json=True)

    else:
        logging.info(f"{ip_name} not found")


def update_testpoint(testplan, row):
    updated = False
    for testpoint in testplan["testpoints"]:
        logging.debug(
            f"Checking {testpoint['name']} == {row['name']} --> {testpoint.get('si_stage')} == {row['si_stage']}"
        )
        if row["name"] == testpoint["name"] and row[
                "si_stage"] != "None" and row["si_stage"] != testpoint.get(
                    "si_stage"):
            logging.debug(
                f"Test {row['name']} should be updated from { testpoint.get('si_stage')} to {row['si_stage']}"
            )
            if row[field] != testpoint.get(field):
                logging.info(
                    f"Updating {row['name']} ->{field} to [{row[field]}]"
                )
                testpoint[field] = row[field]
                updated = True
    return updated


def get_testplan_filename(ip_name, files):
    for file in files:
        if ip_name in file:
            return file
    return None


def export_cmd(args, df: pd.DataFrame):
    df = sort_columns(df)
    df = insert_lc_states_columns(df)

    output_generated = False
    _, extension = os.path.splitext(args.csv)
    if extension == ".csv":
        df.to_csv(args.csv)
        output_generated = True
        print(f"File {args.csv} generated.")
    if args.url:
        gs = (GoogleSheet(args.url) if not args.credentials else GoogleSheet(
            args.url, credentials=args.credentials))
        gs.update(df)
        output_generated = True
        print(f"Updated spreadsheet {args.url}")
    if args.github_token and args.issue_template:
        create_issues(args, df)
        output_generated = True
    if args.bazel_suite:
        export_bazel_suite(args, df)
        output_generated = True

    if not output_generated:
        print("No output specified.")
    return 0


TEST_SUITE_TEMPLATE = """
test_suite(
    name="${sival_stage}_tests",
    tests = [
        % for test in test_list:
        "${test}",
        % endfor
    ]
)
"""


def export_bazel_suite(args, df: pd.DataFrame):
    import numpy as np
    from mako.template import Template
    template = Template(TEST_SUITE_TEMPLATE)
    with open(args.bazel_suite, "w") as file:
        file.write(LICENSE_HEADER.replace("//", "#"))
        sv_stages = ["SV1", "SV2", "SV3"]
        for stage in sv_stages:
            # filter by Sival stage
            sv_tests_df = df[df["si_stage"] == stage].sort_values("bazel")
            # Remove tests without implementation
            sv_tests_df["bazel"].replace(" ", np.nan, inplace=True)
            sv_tests_df["bazel"].replace("", np.nan, inplace=True)
            sv_tests_df.dropna(subset=["bazel"], inplace=True)

            # Generate a list sorted with unique items
            sv_tests = []
            for test in sv_tests_df["bazel"]:
                # Remove the exec_env suffix
                _test = re.sub(r"_fpga.*", "", test)
                _test = re.sub(r"_cw310.*", "", _test)
                sv_tests.extend(re.split(r"\s?,\s?", _test))

            sv_tests = list(sorted(set(sv_tests)))

            # Render the test suite
            test_suite = template.render(sival_stage=stage.lower(), test_list=sv_tests)
            # logging.debug(test_suite)
            file.write(test_suite)
    print(f"Generated {args.bazel_suite}.")
    return 0


def create_issues(args, df: pd.DataFrame):
    repo = hjson.load(open(args.issue_template, "r"))["repository"]
    repo = GithubWrapper(args.github_token, repo)
    repo.load_issues(labels=["Component:ChipLevelTest"])
    issue_template = Template(filename=args.issue_template)

    for _, row in df.fillna("None").iterrows():
        new_issue = hjson.loads(
            issue_template.render(ip_block=row["hw_ip_block"],
                                  test_name=row["name"],
                                  check_list=row["lc_states"].split(", "),
                                  stage=row["si_stage"]))

        if repo.issue_exist(new_issue["title"]):
            print(f"Issue already exists: {new_issue['title']}")
            repo_issue = repo.get_issues(new_issue["title"])[0]
            if repo_issue.body != new_issue["body"]:
                print("Updating the issue")
                repo_issue.edit(body=new_issue["body"],
                                labels=new_issue["labels"])
        else:
            print(f'Create issue: {new_issue["title"]}')
            repo.create_issue(title=new_issue["title"], body=new_issue["body"],\
                                labels=new_issue["labels"], milestone=new_issue["milestone"])

        created += 1
    logging.info(
        "Created %d, Updated %d, Total %d", created, updated, created + updated
    )


class AuthType(Enum):
    # A service account is a special type of Google account intended to represent
    # a non-human user that needs to authenticate and be authorized to access data
    # in Google APIs [sic].
    SERVICE_ACCOUNT = 0
    # This is the case where your application or a script is accessing spreadsheets
    # on behalf of an end user. When you use this scenario, your application or a
    # script will ask the end user (or yourself if you’re running it) to grant access
    # to the user’s data.
    CLIENT_ID = 1


class GoogleSheet:

    def __init__(self,
                 url: str,
                 credentials: str = "~/.config/gspread/credentials.json"):
        self.url = url
        self.credentials = credentials
        self.auth_type = AuthType.CLIENT_ID

        data = json.load(open(os.path.expanduser(self.credentials), "r"))

        if "type" in data.keys() and data["type"] == "service_account":
            self.auth_type = AuthType.SERVICE_ACCOUNT

    def update(self, df: pd.DataFrame):
        import warnings

        import gspread

        warnings.filterwarnings("ignore")

        gc = gspread.oauth(
            credentials_filename=self.credentials
        ) if self.auth_type == AuthType.CLIENT_ID else gspread.service_account(
            filename=self.credentials)

        spreadsheet = gc.open_by_url(args.url)
        try:
            sheet = spreadsheet.worksheet("AutoGenerated")
        except gspread.exceptions.WorksheetNotFound:
            sheet = spreadsheet.add_worksheet(title="AutoGenerated",
                                              rows=len(df),
                                              cols=len(df.columns))

        sheet.update([df.columns.values.tolist()] +
                     df.fillna("None").values.tolist())


def insert_lc_states_columns(df: pd.DataFrame) -> pd.DataFrame:
    lc_states = unique_list(df, "lc_states")
    logging.debug(f"lc_states: {lc_states}")
    df.loc[:, lc_states] = "No"

    def fill_lc_state_column(row):
        for state in lc_states:
            if isinstance(row["lc_states"], str) and state in row["lc_states"]:
                row[state] = "yes"
        return row

    return df.apply(lambda row: fill_lc_state_column(row), axis="columns")


def unique_list(df: pd.DataFrame,
                column: str,
                fillna: str = "NONE") -> list[str]:
    return list(
        set(" ".join(df[column].fillna(fillna).values).replace(",",
                                                               " ").split()))


def sort_columns(df: pd.DataFrame) -> pd.DataFrame:
    colum_order = "hw_ip_block name si_stage desc stage tests features bazel\
                   host_support otp_mutate lc_states tags".split()
    return df[colum_order]


def dataframe_from_testplan(testplan_hjson: str) -> pd.DataFrame:
    testplan = hjson.load(open(testplan_hjson, "r"))

    tests = testplan["testpoints"]
    df = pd.DataFrame.from_dict(tests)

    # For each cell containing a list transform it into a string.
    def list_to_string(val):
        if isinstance(val, list):
            val = ", ".join(val)
        return val

    df = df.map(list_to_string)

    df["hw_ip_block"] = testplan["name"]
    return df.fillna(" ")


if __name__ == "__main__":
    args = parser.parse_args()
    logging.basicConfig(level=args.logging.upper(), filename=args.logging_file)
    sys.exit(main(args))
