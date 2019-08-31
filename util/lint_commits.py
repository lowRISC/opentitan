#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import subprocess
import sys

error_msg_prefix = ''


def error(msg, *args, **kwargs):
    print(error_msg_prefix + msg, file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(
        description='Check commit meta data for common mistakes')
    parser.add_argument('--error-msg-prefix',
                        default='ERROR: ',
                        required=False,
                        help='string to prepend to all error messages')
    parser.add_argument('commitrange',
                        metavar='commit-range',
                        help='git log-compatible commit range to check')
    args = parser.parse_args()

    global error_msg_prefix
    error_msg_prefix = args.error_msg_prefix

    cmd = ['git', 'log', '--pretty=%H;%ae;%an', args.commitrange]
    commits = subprocess.run(cmd,
                             stdout=subprocess.PIPE,
                             check=True,
                             universal_newlines=True).stdout

    has_error = False
    for commit in commits.splitlines():
        (sha, author_email, author_name) = commit.split(';', 3)
        print("Checking commit %s by %s <%s>" %
              (sha, author_name, author_email))
        if author_email.endswith('users.noreply.github.com'):
            error('Author of commit %s has no valid email address set: %s. '
                  'Use "git config user.email user@example.com" to '
                  'set a valid email address, and update the commit '
                  'with "git rebase -i" and/or '
                  '"git commit --amend --reset-author". '
                  'You also need to disable "Keep my email address '
                  'private" in the GitHub email settings.' %
                  (sha, author_email))
            has_error = True

    if has_error:
        error('Commit lint failed.')
        sys.exit(1)


if __name__ == '__main__':
    main()
