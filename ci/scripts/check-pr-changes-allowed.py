#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from fnmatch import fnmatch
import argparse
import sys
import re
import requests

# Number of authorizations required from committers to override a block
NUM_AUTHS_REQD = 2

GH_API_URL = 'https://api.github.com/repos/'


def load_blockfile(blockfile_name: str) -> list[str]:
    blocklist = []
    with open(blockfile_name, 'r') as blockfile:
        for line in blockfile.readlines():
            # Remove everything following a '#' for comments
            line = line.partition('#')[0]
            # Remove leading and trailing whitespace
            line = line.strip()

            # If anything remains after the above add it to the list
            if line != '':
                blocklist.append(line)

    return blocklist


def load_changes(changes_filename: str) -> list[str]:
    with open(changes_filename, 'r') as changes_file:
        changes = changes_file.readlines()
        changes = map(lambda c: c.strip(), changes)
        changes = filter(lambda c: c != '', changes)

    return changes


def check_changes_against_blocklist(changes: list[str],
                                    blocklist: list[str]) -> dict[str,
                                                                  list[str]]:
    """"Determines which changes are blocked by the blocklist

    Returns a dictionary keyed by blocked filenames, the value provides a list
    of the patterns from the blocklist it matched against"""

    blocked_changes = {}

    for change in changes:
        # Create list of patterns from blocklist that match change
        blocked = list(filter(lambda x: x is not None,
                              map(lambda b: b if fnmatch(change, b) else None,
                                  blocklist)))

        # If any match patterns exist add them to the blocked_changes dictionary
        if blocked:
            blocked_changes[change] = blocked

    return blocked_changes


def fetch_pr_comments(gh_token: str, repo_name: str,
                      pr_number: int) -> list[tuple[str, str]]:
    """Fetches comments from a PR and returns a list of (author, comment_body)
    pairs"""

    headers = {
        'Accept': 'application/vnd.github+json',
        'Authorization': f'Bearer {gh_token}',
        'X-GitHub-Api-Version': '2022-11-28'
    }

    pr_comment_url = f'{GH_API_URL}{repo_name}/issues/{pr_number}/comments'
    pr_comment_request = requests.get(pr_comment_url, headers=headers)

    comments_json_list = pr_comment_request.json()
    return [(c['user']['login'], c['body']) for c in comments_json_list]


committer_re = re.compile(r'\* ([\w\s-]+) \(([\w-]+)\)')


def load_committers(committers_filename: str) -> dict[str, str]:
    """Reads a COMMITTERS file and returns a dict mapping handles to names"""

    with open(committers_filename, 'r') as committers_file:
        committer_tuples = committer_re.findall(committers_file.read())

        committers_dict = {ct[1].lower(): ct[0] for ct in committer_tuples}

    if 'githubid' in committers_dict:
        del committers_dict['githubid']

    return committers_dict


authorize_re = re.compile(r'^CHANGE AUTHORIZED: (.*)$', re.MULTILINE)


def get_authorized_changes(comments: list[tuple[str, str]],
                           committers: dict[str, str]) -> dict[str, list[str]]:
    """Returns a dict of file changes authorized by committters.

    The key is the file name, the value is a list of committer handles that
    authorized it.
    """

    file_change_authorizations = {}

    for comment_author, comment_body in comments:
        comment_author = comment_author.lower()

        if comment_author not in committers:
            continue

        file_authorizations = authorize_re.findall(comment_body)
        for filename in file_authorizations:
            filename = filename.strip()

            if filename not in file_change_authorizations:
                file_change_authorizations[filename] = [comment_author]
            else:
                file_change_authorizations[filename].append(comment_author)

    return file_change_authorizations


def main() -> int:
    arg_parser = argparse.ArgumentParser(
        prog='check-pr-changes-allowed',
        description='''Checks a list of changed files supplied as a plain-text
                       list against blocked file patterns. If any match exits
                       with code 1 and the PR should be blocked.''')

    arg_parser.add_argument(
        'changes_file', metavar='changes-file',
        help='plain text file containing a list of changed files')

    arg_parser.add_argument(
        '--block-file', default='BLOCKFILE',
        help='''Plain text file containing path patterns that when matched
                indicate a blocked file.  One pattern per line.''')

    arg_parser.add_argument('--pr-number', type=int,
                            help='ID of the PR requesting the change')

    arg_parser.add_argument(
        '--gh-token', help='''A github access token used to read PR comments
                              for override commands''')

    arg_parser.add_argument(
        '--gh-repo',
        help='Name of the repository on github to read PR comments from',
        default='lowrisc/opentitan')

    args = arg_parser.parse_args()

    blocklist = load_blockfile(args.block_file)
    changes = load_changes(args.changes_file)
    blocked_changes = check_changes_against_blocklist(changes, blocklist)

    # If we've been provided with a github auth token and a PR ref then fetch
    # comments to determine which changes are authorized
    if (args.gh_token is not None and args.pr_number is not None):
        committers = load_committers('COMMITTERS')
        pr_comments = fetch_pr_comments(args.gh_token, args.gh_repo,
                                        args.pr_number)
        authorized_changes = get_authorized_changes(pr_comments, committers)

        block_changes_files = list(blocked_changes.keys())
        for change in block_changes_files:
            # For each changed file that matched the block list check if it's an
            # authorized change
            if (change in authorized_changes and
                    len(authorized_changes[change]) >= NUM_AUTHS_REQD):
                # Change is authorized so delete it from the blocked_changes
                # dict
                del blocked_changes[change]

                authorizers = ', '.join(
                    [f'{committers[handle]} ({handle})' for handle in
                        authorized_changes[change]])
                print(f'{change} change is authorized by {authorizers}')

    if blocked_changes:
        # If there are blocked changes present print out what's been blocked and
        # the pattern(s) that blocked it and return error code 1
        for change, block_patterns in blocked_changes.items():
            patterns_str = ' '.join(block_patterns)
            print(f'{change} blocked by pattern(s): {patterns_str}')

        print('UNAUTHORIZED CHANGES PRESENT, PR cannot be merged!')
        return 1

    print('No unauthorized changes, clear to merge')
    return 0


if __name__ == '__main__':
    sys.exit(main())
