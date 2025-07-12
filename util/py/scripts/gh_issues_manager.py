#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script manages github issues.

usage with a single file:
    ./util/py/scripts/

"""

import argparse
import glob
import json
import logging
import os
import sys
from enum import Enum

import hjson
from github import Auth, Github
from github.GithubObject import NotSet, Opt
from github.Label import Label
from github.NamedUser import NamedUser
from github.Repository import Repository
from mako.template import Template

parser = argparse.ArgumentParser()
parser.add_argument(
    "--logging",
    default="info",
    choices=["debug", "info", "warning", "error", "critical"],
    help="Logging level",
)
parser.add_argument(
    "--token",
    required=True,
    help="""Token""",
)
parser.add_argument(
    "--template",
    required=True,
    help="""Template""",
)


def main(args):

    repo = hjson.load(open(args.template, "r"))["repository"]
    repo = GithubWrapper(args.token, repo)

    issue_template = Template(filename=args.template)
    new_issue = hjson.loads(
        issue_template.render(ip_block="aes",
                              test_name="chip_kmac_smoketest",
                              check_list=["PROD", "DEV", "PROD_END"],
                              stage="SV1"))

    repo.load_issues(labels=new_issue["labels"])

    if repo.issue_exist(new_issue["title"]):
        print(f"Issue already exists")
        repo_issue = repo.issues_by_title(new_issue["title"])[0]
        if repo_issue.body != new_issue["body"]:
            print("Updating the issue")
            repo_issue.edit(body=new_issue["body"],
                            labels=new_issue["labels"],
                            milestone=new_issue["milestone"])
    else:
        print(f'Create issue{new_issue["title"]}')
        repo.create_issue(title=new_issue["title"], body=new_issue["body"],\
                        labels=new_issue["labels"], milestone=new_issue["milestone"])


class GithubWrapper():

    def __init__(self, token, repo):
        auth = Auth.Token(token)
        self.gh = Github(auth=auth)
        self.repo = self.gh.get_repo(repo)
        self.milestones = self.repo.get_milestones()

    def load_issues(self, labels=NotSet, milestone=NotSet):
        self.issues = self.repo.get_issues(labels=labels, milestone=milestone)

    def issues_by_title(self, title):
        return list(filter(lambda ms: ms.title == title, self.issues))

    def search_issues(self, text):
        return list(filter(lambda ms: text in (str(ms.title) + str(ms.body)), self.issues))

    def issue_exist(self, title):
        return len(self.issues_by_title(title)) > 0

    def get_milestone(self, name):
        res = list(filter(lambda ms: ms.title == name, self.milestones))
        return res[0] if len(res) > 0 else NotSet

    def create_issue(
        self,
        title,
        body=NotSet,
        assignee=NotSet,
        milestone=NotSet,
        labels=NotSet,
        assignees=NotSet,
    ):
        if milestone != NotSet:
            milestone = self.get_milestone(milestone)
        return self.repo.create_issue(title, body, assignee, milestone, labels,
                                      assignees)


if __name__ == "__main__":
    args = parser.parse_args()
    logging.basicConfig(level=args.logging.upper())
    sys.exit(main(args))
