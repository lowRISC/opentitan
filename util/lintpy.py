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

# A map from tool name to the tuple (check, fix). These are two commands which
# should be run to check for and fix errors, respectively. If the tool doesn't
# support fixing in place, the "fix" command can be None.
_KNOWN_TOOLS = {
    'yapf': (['yapf', '-d'], ['yapf', '-i']),
    'isort': (['isort', '-c', '-w79'], ['isort', '-w79']),
    'flake8': (['flake8'], None)
}


# include here because in hook case don't want to import reggen
def show_and_exit(clitool, packages):
    util_path = os.path.dirname(os.path.realpath(clitool))
    os.chdir(util_path)
    ver = subprocess.check_output(
        ["git", "describe", "--always", "--dirty", "--broken"],
        universal_newlines=True).strip()
    if not ver:
        ver = 'not found (not in Git repository?)'
    sys.stderr.write(clitool + " Git version " + ver + '\n')
    for p in packages:
        sys.stderr.write(p + ' ' + pkg_resources.require(p)[0].version + '\n')
    sys.exit(0)


def run_linter(tool, dofix, verbose, files):
    '''Run the given lint tool on a nonempty list of files

    Returns (bad, stop) where bad is true if the lint tool spotted any errors.
    stop is true if the tool fails and either dofix is false or the tool
    doesn't have a fix command.

    '''
    assert files
    assert tool in _KNOWN_TOOLS
    check, fix = _KNOWN_TOOLS[tool]

    if verbose:
        print('Running {}'.format(' '.join(check)))

    check_cmd = check + files
    try:
        assert check
        subprocess.check_output(check_cmd, stderr=subprocess.STDOUT)
        return (False, False)
    except FileNotFoundError:
        print('{} not found: do you need to install it?'.format(check[0]))
        return (True, True)
    except subprocess.CalledProcessError as exc:
        sys.stderr.write('Lint failed:\n  {}\n'.format(' '.join(check_cmd)))
        if not dofix or fix is None:
            return (True, True)

        if exc.output:
            output = exc.output.decode(sys.getfilesystemencoding())
            print('\t',
                  '\n\t'.join(output.splitlines()),
                  sep='',
                  file=sys.stderr)

    print("Fixing...", file=sys.stderr)
    subprocess.check_call(fix + files,
                          stderr=subprocess.STDOUT,
                          stdout=subprocess.DEVNULL)
    return (True, False)


def lint_files(tools, input_files, dofix, verbose):
    '''Run each tool on each file in input_files.'''
    something_bad = False

    if verbose:
        print('Changed files: ' + ', '.join(input_files))

    for tool in tools:
        bad, stop = run_linter(tool, dofix, verbose, input_files)
        if bad:
            something_bad = True
        if stop:
            break

    return 1 if something_bad else 0


def get_files_from_git(show_cached):
    '''Return a list of paths to work on

    Use git diff to find the list of Python files that have changed. If
    show_cached is True, this operates on the staging tree, rather than the
    work tree.

    '''
    # This git diff command will return all the paths that have changed and end
    # in .py
    cmd = (['git', 'diff', '--name-only', '--diff-filter=ACM'] +
           (['--cached'] if show_cached else []) + ['*.py'])

    lines = subprocess.check_output(cmd, universal_newlines=True).split('\n')
    paths = []
    for line in lines:
        path = line.strip()
        if path:
            paths.append(path)

    return paths


def parse_tool_list(as_string):
    '''Parse a list of tools (as passed to the --tools argument)

    Returns a nonempty list of strings, one for each tool included.'''
    tools = []
    for name in as_string.split(','):
        name = name.strip()
        if name not in _KNOWN_TOOLS:
            raise argparse.ArgumentTypeError('Unknown tool: {}.'.format(name))
        tools.append(name)

    assert tools
    return tools


def install_commit_hook():
    '''Install this script as a pre-commit hook in this repository'''
    git_dir = subprocess.check_output(['git', 'rev-parse', '--git-dir'],
                                      universal_newlines=True).strip()
    hooks_dir = os.path.join(git_dir, 'hooks')
    os.makedirs(hooks_dir, exist_ok=True)

    hook_path = os.path.join(hooks_dir, 'pre-commit')
    if os.path.exists(hook_path):
        raise RuntimeError('There is already a hook at {}.'.format(hook_path))

    # Find a relative path from hooks_dir to __file__ (so we can move the whole
    # repo in the future without breaking anything).
    rel_path = os.path.relpath(__file__, hooks_dir)

    print('Installing hook at {}, pointing at {}.'.format(hook_path, rel_path))
    os.symlink(rel_path, hook_path)


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
        help=('Only check files staged for commit rather than'
              'all modified files (forced when run as git hook)'))
    parser.add_argument('--fix',
                        action='store_true',
                        help='Fix files detected with problems')
    parser.add_argument('--hook',
                        action='store_true',
                        help='Install as ../.git/hooks/pre-commit and exit')
    parser.add_argument('-f',
                        '--file',
                        metavar='file',
                        nargs='+',
                        default=[],
                        help='File(s) to check instead of deriving from git')
    parser.add_argument('--tools',
                        type=parse_tool_list,
                        default=['yapf', 'isort'],
                        help='Comma separated list of linting tools to use')

    args = parser.parse_args()
    if args.version:
        show_and_exit(__file__, ['yapf', 'isort', 'flake8'])

    running_hook = sys.argv[0].endswith('hooks/pre-commit')
    if running_hook and args.verbose:
        print('argv[0] is ' + sys.argv[0] + ' so running_hook is True')

    if args.hook:
        if args.file:
            raise RuntimeError('Cannot specify both --hook and a file list.')
        install_commit_hook()
        return 0

    if args.file:
        input_files = args.file
        if args.commit:
            raise RuntimeError('Cannot specify both --commit and a file list.')
    else:
        input_files = get_files_from_git(running_hook or args.commit)

    if not input_files:
        print('No input files. Exiting.')
        return 0

    return lint_files(args.tools, input_files, args.fix, args.verbose)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(1)
