#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import re
import sys

from git import Repo

error_msg_prefix = 'ERROR: '
warning_msg_prefix = 'WARNING: '

# Maximum length of the summary line in the commit message (the first line)
# There is no hard limit, but a typical convention is to keep this line at or
# below 50 characters, with occasional outliers.
COMMIT_MSG_MAX_SUMMARY_LEN = 100


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
            f'Commit author has no valid email address set: '
            '{commit.author.email!r}. '
            'Use "git config user.email user@example.com" to '
            'set a valid email address, then update the commit '
            'with "git rebase -i" and/or '
            '"git commit --amend --signoff --reset-author". '
            'Also check your GitHub settings at '
            'https://github.com/settings/emails: your email address '
            'must be verified, and the option "Keep my email address '
            'private" must be disabled. '
            'This command will also sign off your commit indicating agreement '
            'to the Contributor License Agreement. See CONTRIBUTING.md for '
            'more details.', commit)
        success = False

    if ' ' not in commit.author.name:
        warning(
            f'The commit author name {commit.author.name!r} contains no space. '
            'Use "git config user.name \'Johnny English\'" to '
            'set your real name, and update the commit with "git rebase -i " '
            'and/or "git commit --amend --signoff --reset-author". '
            'This command will also sign off your commit indicating agreement '
            'to the Contributor License Agreement. See CONTRIBUTING.md for '
            'more details.', commit)
        # A warning doesn't fail lint.

    return success


def lint_commit_message(commit):
    success = True
    lines = commit.message.splitlines()

    # Check length of summary line.
    summary_line_len = len(lines[0])
    if summary_line_len > COMMIT_MSG_MAX_SUMMARY_LEN:
        error(
            "The summary line in the commit message is %d characters long; "
            "only %d characters are allowed." %
            (summary_line_len, COMMIT_MSG_MAX_SUMMARY_LEN), commit)
        success = False

    # Check for an empty line separating the summary line from the long
    # description.
    if len(lines) > 1 and lines[1] != "":
        error(
            "The second line of a commit message must be empty, as it "
            "separates the summary from the long description.", commit)
        success = False

    # Check that the commit message contains at least one Signed-off-by line
    # that matches the author name and email. There might be other signoffs (if
    # there are multiple authors). We don't have any requirements about those
    # at the moment and just pass them through.
    signoff_lines = []
    signoff_pfx = 'Signed-off-by: '
    for idx, line in enumerate(lines):
        if not line.startswith(signoff_pfx):
            continue

        signoff_body = line[len(signoff_pfx):]
        match = re.match(r'[^<]+ <[^>]*>$', signoff_body)
        if match is None:
            error('Commit has Signed-off-by line {!r}, but the second part '
                  'is not of the required form. It should be of the form '
                  '"Signed-off-by: NAME <EMAIL>".'
                  .format(line))
            success = False

        signoff_lines.append(line)

    expected_signoff_line = ("Signed-off-by: {} <{}>"
                             .format(commit.author.name,
                                     commit.author.email))
    signoff_req_msg = ('The commit message must contain a Signed-off-by line '
                       'that matches the commit author name and email, '
                       'indicating agreement to the Contributor License '
                       'Agreement. See CONTRIBUTING.md for more details. '
                       'You can use "git commit --signoff" to ask git to add '
                       'this line for you.')

    if not signoff_lines:
        error('Commit has no Signed-off-by line. ' + signoff_req_msg)
        success = False
    elif expected_signoff_line not in signoff_lines:
        error(('Commit has one or more Signed-off-by lines, but not the one '
               'we expect. We expected to find "{}". '
               .format(expected_signoff_line)) +
              signoff_req_msg)
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
        description='Check commit metadata for common mistakes')
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
                        help=('commit range to check '
                              '(must be understood by git log)'))
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
