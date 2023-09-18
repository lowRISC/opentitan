#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''
This script may be used along with the example HJSON data file in
`util/py/data/gh_issue_template.hjson` to automatically file issues to the
OpenTitan GitHub for task management purposes.

Dry-run usage:
    ./util/py/scripts/create_gh_issues.py --dryrun <HJSON data file>

Actual usage:
    ./util/py/scripts/create_gh_issues.py <HJSON data file>

Before using this script, you must:
1. have the GitHub CLI installed (see https://github.com/cli/cli#installation),
2. create a personal authentication token for you GH account:
   https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens#creating-a-fine-grained-personal-access-token
3. authenticate the CLI client with the token you created above, using:
   `gh auth login --with-token <token>`
'''

import argparse
import json
import subprocess
import sys
import time
from pprint import pprint

import hjson

UPSTREAM = "lowRISC/opentitan"


def run(cmd):
    while True:
        try:
            return subprocess.run(cmd,
                                  stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE,
                                  check=True,
                                  text=True,
                                  shell=True)
            break
        except BaseException as e:
            pprint(e.stdout)
            pprint(e.stderr)
            time.sleep(5)


def get_valid_labels_set(repo):
    check_cmd = f"gh label list --repo {repo} --json name -L 150"
    valid_labels = set()
    for valid_label in json.loads(run(check_cmd).stdout):
        valid_labels.add(valid_label["name"])
    return valid_labels


def create_issue(repo, issue, valid_labels, dryrun):
    title = issue["title"]
    body = issue["body"]
    labels = issue["labels"]
    assignee = issue["assignee"]
    milestone = issue["milestone"]
    project = issue["project"]
    priority = issue["priority"]

    # Create issue.
    create_cmd = f"gh issue create --repo {repo} --title '{title}'"
    create_cmd += f"--body '{body}' --project {project}"
    if assignee:
        create_cmd += f" --assignee '{assignee}'"
    if milestone:
        create_cmd += f" --milestone '{milestone}'"
    for label in labels:
        # Check labels are valid.
        if label in valid_labels:
            create_cmd += f" --label '{label}'"
        else:
            print(f"Error: invalid label {label} for repo {repo}")
            sys.exit(1)
    if priority and priority in ["P1", "P2", "P3"]:
        create_cmd += f" --label 'Priority:{priority}'"
    if dryrun:
        print("Command to be run:")
        print(create_cmd)
        print()
    else:
        run(create_cmd)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dryrun",
                        action='store_true',
                        help="Path of the issue hjson file.")
    parser.add_argument("issue_hjson", help="Path of the issue hjson file.")
    args = parser.parse_args()

    issues = None
    with open(args.issue_hjson, 'r') as hjson_file:
        issues = hjson.load(hjson_file)

    valid_labels = get_valid_labels_set(UPSTREAM)
    for issue in issues:
        create_issue(UPSTREAM, issue, valid_labels, args.dryrun)


if __name__ == "__main__":
    main()
