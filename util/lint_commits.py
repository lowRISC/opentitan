#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import subprocess
import sys

from git import Repo

error_msg_prefix = 'ERROR: '
warning_msg_prefix = 'WARNING: '

# Maximum length of the summary line in the commit message (the first line)
# There is no hard limit, but a typical convention is to keep this line at or
# below 50 characters, with occasional outliers.
COMMIT_MSG_MAX_SUMMARAY_LEN = 100


def error(msg, commit=None):
    full_msg = msg
    if commit:
        full_msg = "Commit %s: %s" % (commit.hexsha, msg)
    print(error_msg_prefix + full_msg, file=sys.stderr)


def warning(msg, commit=None):
    full_msg = msg
    if commit:
        full_msg = "Commit %s: %s" % (commit.hexsha, msg)
    print(warning_msg_prefix + full_msg, file=sys.stderr)


def lint_commit_author(commit):
    success = True
    if commit.author.email.endswith('users.noreply.github.com'):
        error(
            'Commit author has no valid email address set: %s. '
            'Use "git config user.email user@example.com" to '
            'set a valid email address, and update the commit '
            'with "git rebase -i" and/or '
            '"git commit --amend --reset-author". '
            'Also check your GitHub settings at '
            'https://github.com/settings/emails: your email address '
            'must be verified, and the option "Keep my email address '
            'private" must be disabled.' % (commit.author.email, ), commit)
        success = False

    if not ' ' in commit.author.name:
        warning(
            'The commit author name "%s" does contain no space. '
            'Use "git config user.name \'Johnny English\'" to '
            'set your real name, and update the commit with "git rebase -i " '
            'and/or "git commit --amend --reset-author".' %
            (commit.author.name, ), commit)
        # A warning doesn't fail lint.

    return success


def lint_commit_message(commit):
    success = True
    lines = commit.message.splitlines()

    # Check length of summary line.
    summary_line_len = len(lines[0])
    if summary_line_len > COMMIT_MSG_MAX_SUMMARAY_LEN:
        error(
            "The summary line in the commit message %d characters long, "
            "only %d characters are allowed." %
            (summary_line_len, COMMIT_MSG_MAX_SUMMARAY_LEN), commit)
        success = False

    # Check for an empty line separating the summary line from the long
    # description.
    if len(lines) > 1 and lines[1] != "":
        error(
            "The second line of a commit message must be empty, as it "
            "separates the summary from the long description.", commit)
        success = False

    # Check that the commit message contains a Signed-off-by line which
    # matches the author name and email metadata.
    expected_signoff_line = "Signed-off-by: %s <%s>" % (commit.author.name,
                                                        commit.author.email)
    if expected_signoff_line not in lines:
        error(
            'The commit message must contain a Signed-off-by line that '
            'matches the commit author name and email, indicating agreement '
            'to the Contributor License Agreement. See CONTRIBUTING.md for '
            'more details. "git commit -s" can be used to have git add this '
            'line for you.')
        success = False

    return success


def lint_commit(commit):
    success = True
    if not lint_commit_author(commit):
        success = False
    if not lint_commit_message(commit):
        success = False
    return success


def main():
    global error_msg_prefix
    global warning_msg_prefix

    parser = argparse.ArgumentParser(
        description='Check commit meta data for common mistakes')
    parser.add_argument('--error-msg-prefix',
                        default=error_msg_prefix,
                        required=False,
                        help='string to prepend to all error messages')
    parser.add_argument('--warning-msg-prefix',
                        default=warning_msg_prefix,
                        required=False,
                        help='string to prepend to all warning messages')
    parser.add_argument('--no-merges',
                        required=False,
                        action="store_true",
                        help='do not check commits with more than one parent')
    parser.add_argument('commit_range',
                        metavar='commit-range',
                        help='git log-compatible commit range to check')
    args = parser.parse_args()

    error_msg_prefix = args.error_msg_prefix
    warning_msg_prefix = args.warning_msg_prefix

    lint_successful = True

    repo = Repo()
    commits = repo.iter_commits(args.commit_range)
    for commit in commits:
        print("Checking commit %s" % commit.hexsha)
        is_merge = len(commit.parents) > 1
        if is_merge and args.no_merges:
            print("Skipping merge commit.")
            continue

        if not lint_commit(commit):
            lint_successful = False

    if not lint_successful:
        error('Commit lint failed.')
        sys.exit(1)


if __name__ == '__main__':
    main()
