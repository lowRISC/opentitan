#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from fnmatch import fnmatch
import argparse
import sys
import re
import requests
from datetime import datetime, timezone

NUM_AUTHS_REQD = 2

GH_API_URL = 'https://api.github.com/repos/'


def load_blockfile(blockfile_name: str) -> list[str]:
    blocklist = []
    with open(blockfile_name, 'r') as blockfile:
        for line in blockfile.readlines():
            line = line.partition('#')[0]
            line = line.strip()
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
    """Return dict mapping blocked filenames to matching patterns."""

    blocked_changes = {}

    for change in changes:
        blocked = list(filter(lambda x: x is not None,
                              map(lambda b: b if fnmatch(change, b) else None,
                                  blocklist)))
        if blocked:
            blocked_changes[change] = blocked

    return blocked_changes


def fetch_pr_comments(gh_token: str, repo_name: str,
                      pr_number: int) -> list[tuple[str, str, str]]:
    """Return list of (author, body, created_at) for issue comments."""

    headers = {
        'Accept': 'application/vnd.github+json',
        'Authorization': f'Bearer {gh_token}',
        'X-GitHub-Api-Version': '2022-11-28'
    }

    pr_comment_url = f'{GH_API_URL}{repo_name}/issues/{pr_number}/comments'
    resp = requests.get(pr_comment_url, headers=headers)
    resp.raise_for_status()

    comments_json_list = resp.json()
    return [(c['user']['login'], c['body'], c.get('created_at'))
            for c in comments_json_list]


def fetch_pr_reviews(gh_token: str, repo_name: str,
                     pr_number: int) -> list[tuple[str, str, str, str]]:
    """Return list of APPROVED reviews as (author, body, state, submitted_at)."""

    headers = {
        'Accept': 'application/vnd.github+json',
        'Authorization': f'Bearer {gh_token}',
        'X-GitHub-Api-Version': '2022-11-28'
    }

    pr_reviews_url = f'{GH_API_URL}{repo_name}/pulls/{pr_number}/reviews'
    resp = requests.get(pr_reviews_url, headers=headers)
    resp.raise_for_status()

    reviews_json = resp.json()
    results: list[tuple[str, str, str, str]] = []
    for r in reviews_json:
        state = r.get('state', '')
        if state != 'APPROVED':
            continue
        author = r['user']['login'] if r.get('user') else ''
        results.append((author, r.get('body', ''), state,
                        r.get('submitted_at')))

    return results


def fetch_pr_last_commit_time(gh_token: str, repo_name: str,
                              pr_number: int) -> datetime:
    """Return datetime of the PR's last commit (UTC)."""

    headers = {
        'Accept': 'application/vnd.github+json',
        'Authorization': f'Bearer {gh_token}',
        'X-GitHub-Api-Version': '2022-11-28'
    }

    commits_url = f'{GH_API_URL}{repo_name}/pulls/{pr_number}/commits'
    resp = requests.get(commits_url, headers=headers)
    resp.raise_for_status()
    commits = resp.json()

    if not commits:
        return datetime.fromtimestamp(0, tz=timezone.utc)
    last = commits[-1]
    date_str = None
    try:
        date_str = last['commit']['committer']['date']
    except Exception:
        date_str = last['commit']['author']['date']

    if date_str.endswith('Z'):
        date_str = date_str.replace('Z', '+00:00')
    return datetime.fromisoformat(date_str)


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


def get_authorized_changes(comments: list[tuple[str, str, str]],
                           reviews: list[tuple[str, str, str, str]],
                           committers: dict[str, str],
                           last_commit_time: datetime) -> dict[str, set[str]]:
    """Return mapping file -> set(handles) for valid authorizations.

    Only counts authorizations submitted after last_commit_time.
    """

    file_change_authorizations: dict[str, set[str]] = {}

    def _process_entry(author: str, body: str, when_str: str) -> None:
        if not when_str:
            return
        author_l = author.lower()
        if author_l not in committers:
            return
        try:
            when = datetime.fromisoformat(
                when_str.replace('Z', '+00:00') if when_str.endswith('Z') else when_str)
        except Exception:
            return
        if when <= last_commit_time:
            return
        for filename in authorize_re.findall(body):
            fn = filename.strip()
            file_change_authorizations.setdefault(fn, set()).add(author_l)

    for author, body, created_at in comments:
        _process_entry(author, body, created_at)
    for author, body, state, submitted_at in reviews:
        _process_entry(author, body, submitted_at)

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

    arg_parser.add_argument(
        '--plain-block-msg',
        help='''Just outputs the path of each blocked file with no further
                information''',
        action='store_true')

    arg_parser.add_argument(
        '--report-unused-patterns',
        help='Produces a list of block patterns that did not block anything',
        action='store_true')

    args = arg_parser.parse_args()

    blocklist = load_blockfile(args.block_file)
    changes = load_changes(args.changes_file)
    blocked_changes = check_changes_against_blocklist(changes, blocklist)

    if (args.gh_token is not None and args.pr_number is not None):
        committers = load_committers('COMMITTERS')
        # fetch comments, reviews and last commit time
        pr_comments = fetch_pr_comments(args.gh_token, args.gh_repo,
                                        args.pr_number)
        pr_reviews = fetch_pr_reviews(args.gh_token, args.gh_repo,
                                      args.pr_number)
        last_commit_time = fetch_pr_last_commit_time(args.gh_token,
                                                    args.gh_repo,
                                                    args.pr_number)

        authorized_changes = get_authorized_changes(pr_comments,
                                                   pr_reviews,
                                                   committers,
                                                   last_commit_time)

        block_changes_files = list(blocked_changes.keys())
        for change in block_changes_files:
            if (change in authorized_changes and
                    len(authorized_changes[change]) >= NUM_AUTHS_REQD):
                del blocked_changes[change]
                authorizers = ', '.join(
                    [f'{committers[handle]} ({handle})' for handle in
                        authorized_changes[change]])
                if not args.plain_block_msg:
                    print(f'{change} change is authorized by {authorizers}')

    if args.report_unused_patterns:
        unused_patterns = set(blocklist)

        used_patterns = set(sum(blocked_changes.values(), []))
        unused_patterns = set(blocklist) - used_patterns

        if unused_patterns:
            print('WARNING: Unused patterns have been found:')

            for pattern in unused_patterns:
                print(pattern)

            print('')

    if blocked_changes:
        # print blocked changes and return error code 1
        for change, block_patterns in blocked_changes.items():
            patterns_str = ' '.join(block_patterns)
            if args.plain_block_msg:
                print(change)
            else:
                print(f'{change} blocked by pattern(s): {patterns_str}')

        if not args.plain_block_msg:
            print('UNAUTHORIZED CHANGES PRESENT, PR cannot be merged!')

        return 1

    print('No unauthorized changes, clear to merge')
    return 0


if __name__ == '__main__':
    sys.exit(main())
