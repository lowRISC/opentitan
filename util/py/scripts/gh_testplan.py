#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import copy
import json
import logging
import subprocess
import sys

import hjson

UPSTREAM = "lowRISC/opentitan"
COPYRIGHT_HEADER = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

"""

flags = argparse.ArgumentParser(description="Testplan to github issue utility")
flags.add_argument('--logging',
                   default='info',
                   choices=['debug', 'info', 'warning', 'error', 'critical'],
                   help='Logging level')
flags.add_argument('--gh_bin', default='gh', help="Github CLI binary")
flags.add_argument('--repo', default=UPSTREAM, help="Upstream repo")
flags.add_argument('--dry-run',
                   action=argparse.BooleanOptionalAction,
                   default=True,
                   help='Do not perform any github API actions')
flags.add_argument('testplan', type=str, help='The testplan to process')


class Testplan(object):

    def __init__(self, filename):
        self.filename = filename

    def load(self):
        plan = hjson.load(open(self.filename))
        testpoints = {}
        # For ease of use, we use a dict as the in-memory representation.
        for p in plan['testpoints']:
            if p['name'] in testpoints:
                raise Exception('Duplicate testpoint name', p['name'])
            testpoints[p['name']] = p
        plan['testpoints'] = testpoints
        self.plan = plan

    def save(self):
        plan = copy.copy(self.plan)
        plan['testpoints'] = list(plan['testpoints'].values())
        with open(self.filename, 'wt') as fp:
            fp.write(COPYRIGHT_HEADER)
            hjson.dump(plan, fp)

    def keys(self):
        return self.plan['testpoints'].keys()

    def get(self, key, default):
        return self.plan['testpoints'].get(key, default)

    def put(self, key, value):
        self.plan['testpoints'][key] = value

    def github_issue_template(self, key):
        result = copy.copy(self.plan['github_issue_template'])
        testpoint = self.plan['testpoints'][key]
        result.update(testpoint.get('github', {}))
        return result


class GithubApi(object):

    def __init__(self, gh, repo, dry_run=False):
        self.gh = gh
        self.repo = repo
        self.dry_run = dry_run

    @staticmethod
    def call(args, dry_run=False):
        """Call a subprocess.

        Args:
          args: List[str]; List of arguments.
          dry_run: bool; If true, print the command that would have been called.
        """
        if dry_run:
            print("===== DRY_RUN =====")
            for a in args:
                print(f" '{a}'", end='')
            print()
            return ''
        else:
            return subprocess.check_output(args)

    def get_valid_labels(self):
        """Get the valid labels for the repo.

        Returns:
          Set[str]: Valid labels.
        """
        result = set()
        cmd = [
            'gh', 'label', 'list', '--repo', self.repo, '--json', 'name', '-L',
            '1500'
        ]
        for label in json.loads(self.call(cmd)):
            result.add(label['name'])
        return result

    def create_issue(self, issue):
        """Create an issue in the repo.

        Args:
          issue: Dict[str]; Issue to create.
        Returns:
          str: The url of the created issue.
        """
        cmd = [
            'gh',
            'issue',
            'create',
            '--repo',
            self.repo,
            '--title',
            issue['title'],
            '--body',
            issue['body'],
        ]
        if 'project' in issue:
            cmd.extend(['--project', issue['project']])
        if 'assignee' in issue:
            cmd.extend(['--assignee', issue['assignee']])
        if 'milestone' in issue:
            cmd.extend(['--milestone', issue['milestone']])

        for label in issue.get('labels', []):
            cmd.extend(['--label', label])
        priority = issue.get('priority')
        if priority in ('P1', 'P2', 'P3'):
            cmd.extend(['--label', f'Priority:{priority}'])
        return self.call(cmd, self.dry_run)


def create_issues(testplan, gh):
    """Create issues in the testplan.

    Creates the issues in the testplan and updates the testplan with the
    URLs of the created issues.  Issues that already have a URL will not
    be re-created.

    Args:
      testplan: Testplan; the Testplan object holding the test descriptions.
      gh: GithubApi; a GithubApi instance.
    """
    allowed_labels = gh.get_valid_labels()
    for key in testplan.keys():
        # First get the issue creation template from the testplan
        # and check if the issue has already been created.
        template = testplan.github_issue_template(key)
        if template.get('url'):
            # Already created
            continue

        # Fill in the necessary fields in the template for issue creation.
        testpoint = testplan.get(key, None)
        for label in template.get('labels', []):
            if label not in allowed_labels:
                raise Exception(
                    f'Bad label {label!r} in {testpoint["name"]!r}')
        desc = testpoint['desc']
        (title, blank, body) = desc.split('\n', 2)
        if blank.strip():
            raise Exception(f'Malformed "desc" in {testpoint["name"]}')
        template['title'] = title
        template['body'] = body

        # Create the issue, then update the testpoint with the URL.
        # Save the testplan so if there is a crash later, we've
        # recorded that we created this issue.
        url = gh.create_issue(template)
        if 'github' not in testpoint:
            testpoint['github'] = {}
        testpoint['github']['url'] = url
        testplan.save()


def main(args):
    gh = GithubApi(args.gh_bin, args.repo, args.dry_run)
    testplan = Testplan(args.testplan)
    testplan.load()
    create_issues(testplan, gh)


if __name__ == '__main__':
    args = flags.parse_args()
    logging.basicConfig(level=args.logging.upper())
    sys.exit(main(args))
