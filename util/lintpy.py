#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Lint Python for lowRISC rules"""

import argparse
import os
import subprocess
import sys

import pkg_resources


# include here because in hook case don't want to import reggen
def show_and_exit(clitool, packages):
    util_path = os.path.dirname(os.path.realpath(clitool))
    os.chdir(util_path)
    ver = subprocess.run(
        ["git", "describe", "--always", "--dirty", "--broken"],
        stdout=subprocess.PIPE).stdout.strip().decode('ascii')
    if (ver == ''):
        ver = 'not found (not in Git repository?)'
    sys.stderr.write(clitool + " Git version " + ver + '\n')
    for p in packages:
        sys.stderr.write(p + ' ' + pkg_resources.require(p)[0].version + '\n')
    exit(0)


def check_linter(cmd, cmdfix, dofix, verbose, files, **kwargs):
    if not files:
        return
    if verbose:
        print('Running %s' % cmd[0])
    try:
        subprocess.check_output(
            cmd + files, stderr=subprocess.STDOUT, **kwargs)
        return 0
    except FileNotFoundError:
        print('%s not found: do you need to install it?' % cmd[0])
        return 1
    except subprocess.CalledProcessError as exc:
        print('Lint failed:', file=sys.stderr)
        print(' '.join(exc.cmd), file=sys.stderr)
        if exc.output:
            output = exc.output.decode(sys.getfilesystemencoding())
            print(
                '\t',
                '\n\t'.join(output.splitlines()),
                sep='',
                file=sys.stderr)
        if dofix:
            print("Fixing...", file=sys.stderr)
            subprocess.check_output(
                cmdfix + files, stderr=subprocess.STDOUT, **kwargs)
        return 1


def filter_ext(extension, files, exclude=None):
    files = [f for f in files if f.endswith(extension)]
    if exclude is not None:
        files = [i for i in files if exclude not in i]
    return files


def lint_files(changed_files, dofix, verbose):
    err = 0
    if not isinstance(changed_files, list):
        changed_files = [
            i.strip() for i in changed_files.splitlines()
            if '/external/' not in i
        ]

    changed_extensions = {
        ext
        for root, ext in map(os.path.splitext, changed_files)
    }
    if verbose:
        print('Changed files: ' + str(changed_files))
        print('Changed extensions: ' + str(changed_extensions))

    if '.py' in changed_extensions:
        py_files = filter_ext('.py', changed_files)
        err += check_linter(['yapf', '-d'], ['yapf', '-i'], dofix, verbose,
                            py_files)
        err += check_linter(['isort', '-c', '-w79'], ['isort', '-w79'], dofix,
                            verbose, py_files)

    # could do similar checks for other file types
    return err


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument(
        '--version', action='store_true', help='Show version and exit')
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Verbose output: ls the output directories')
    parser.add_argument(
        '-c',
        '--commit',
        action='store_true',
        help='Only check files staged for commit rather than' \
             'all modified files (forced when run as git hook)')
    parser.add_argument(
        '--fix', action='store_true', help='Fix files detected with problems')
    parser.add_argument(
        '--hook',
        action='store_true',
        help='Install as ../.git/hooks/pre-commit and exit')
    parser.add_argument(
        '-f',
        '--file',
        metavar='file',
        nargs='+',
        default=[],
        help='File(s) to check instead of deriving from git')

    args = parser.parse_args()
    if args.version:
        show_and_exit(__file__, ['yapf', 'isort'])

    util_path = os.path.dirname(os.path.realpath(__file__))
    repo_root = os.path.abspath(os.path.join(util_path, os.pardir))
    # check for running as a hook out of $(TOP)/.git/hooks
    # (symlink will already have this correct)
    if repo_root.endswith('.git'):
        repo_root = os.path.abspath(os.path.join(repo_root, os.pardir))
    running_hook = sys.argv[0].endswith('hooks/pre-commit')

    if args.verbose:
        print('argv[0] is ' + sys.argv[0] + ' so running_hook is ' +
              str(running_hook))
        print('util_path is ' + util_path)
        print('repo_root is ' + repo_root)

    if len(args.file) > 0:
        changed_files = args.file
    else:

        os.chdir(repo_root)
        if not os.path.isdir(os.path.join(repo_root, '.git')):
            print(
                "Script not in expected location in a git repo",
                file=sys.stderr)
            sys.exit(1)

        if args.hook:
            subprocess.run(
                'ln -s ../../util/lintpy.py .git/hooks/pre-commit'.split())
            sys.exit(0)

        if running_hook or args.commit:
            diff_cmd = 'git diff --cached --name-only --diff-filter=ACM'
        else:
            diff_cmd = 'git diff --name-only --diff-filter=ACM'

        changed_files = subprocess.check_output(diff_cmd.split())
        changed_files = changed_files.decode(sys.getfilesystemencoding())

    sys.exit(lint_files(changed_files, args.fix, args.verbose))


if __name__ == "__main__":
    main()
