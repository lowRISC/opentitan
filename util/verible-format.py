#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import shutil
import sys
import os
import argparse
import subprocess
import logging
import difflib

logger = logging.getLogger('verible_format')

VERIBLE_ARGS = ["--formal_parameters_indentation=indent",
                "--named_parameter_indentation=indent",
                "--named_port_indentation=indent",
                "--port_declarations_indentation=indent"]


def get_repo_top():
    return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True, universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()


def get_verible_executable_path():
    return shutil.which('verible-verilog-format')


def get_verible_version(verible_exec_path):
    return subprocess.run([verible_exec_path, '--version'],
                          check=True, universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip().split('\n')[0]


def process_file(filename_abs, verible_exec_path,
                 inplace=False, show_diff=False, show_cst=False):
    args = [verible_exec_path] + VERIBLE_ARGS
    if inplace:
        args.append('--inplace')
    args.append(filename_abs)

    verible = subprocess.run(args, check=False, universal_newlines=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    ret = 0

    if len(verible.stderr) > 0:
        logger.info('ERROR: ' + str(filename_abs))
        logger.debug(verible.stderr)
        ret = 1
    elif not inplace:
        with open(filename_abs, 'r') as fp:
            orig = fp.read().split('\n')

        formatted = verible.stdout.split('\n')

        diff = list(difflib.unified_diff(orig, formatted, lineterm='', n=3,
                                         fromfile=filename_abs,
                                         tofile=filename_abs + '.formatted'))
        ret = len(diff) > 0

        if not show_diff and len(diff) > 0:
            logger.info('File differs: ' + filename_abs)

        if show_diff and len(diff) > 0:
            logger.info('')
            for line in diff:
                logger.info(line)

        if len(diff) > 0 and show_cst:
            cst = subprocess.run(['verible-verilog-syntax',
                                  '--printtree', filename_abs],
                                 check=False, universal_newlines=True,
                                 stdout=subprocess.PIPE)
            logger.info(cst.stdout)

    return ret


def main():
    parser = argparse.ArgumentParser(description='Format source code with Verible formatter')
    parser.add_argument('-q', '--quiet', action='store_true', default=False,
                        help='print only errors and warnings')
    parser.add_argument('-v', '--verbose', action='store_true', default=False,
                        help='print extra debug messages')
    parser.add_argument('--show-diff', action='store_true', default=False,
                        help='print diff (when files differ)')
    parser.add_argument('--show-cst', action='store_true', default=False,
                        help='print CST tree')
    parser.add_argument('--progress', action='store_true', default=False,
                        help='show progress')
    parser.add_argument('--inplace', action='store_true', default=False,
                        help='format files in place (overwrite original files)')
    parser.add_argument('-l', '--allowlist', action='store_true', default=False,
                        help='process only files from allow list')
    parser.add_argument('-a', '--all', action='store_true', default=False,
                        help='process all files in repository (.sv and .svh)')
    parser.add_argument('-f', '--files', metavar='file', type=str, nargs='+', default=[],
                        help='process provided files')
    args = parser.parse_args()

    if not args.quiet:
        logger.addHandler(logging.StreamHandler())
        logger.setLevel(logging.INFO)

        if args.verbose:
            logger.setLevel(logging.DEBUG)

    if args.inplace:
        logger.warning('WARNING: Operating in-place - so make sure to make a backup or '
                       'run this on an experimental branch')

    verible_exec_path = get_verible_executable_path()

    if not verible_exec_path:
        logger.error('verible-verilog-format either not installed or not visible in PATH')
        sys.exit(1)
    else:
        logger.info('Using Verible formatter version: ' + get_verible_version(verible_exec_path))

    logger.debug('repo_top: ' + get_repo_top())
    logger.debug('verible exec: ' + verible_exec_path)
    logger.debug('verible args: ' + str(VERIBLE_ARGS))

    repo_top_dir = get_repo_top()

    verible_files = []

    for f in args.files:
        filename_abs = f

        # Prepend repository absolute top path if relative path given
        if f[0:1] != '/':
            filename_abs = repo_top_dir + '/' + filename_abs

        if os.path.exists(filename_abs):
            verible_files.append(filename_abs)

    if args.allowlist:
        with open(repo_top_dir + '/util/verible-format-allowlist.txt', 'r') as fp:
            for line in fp:
                if line[0] == '#':
                    continue

                filename = line.strip()

                if len(filename) == 0:
                    continue

                filename_abs = repo_top_dir + '/' + filename
                if os.path.exists(filename_abs):
                    verible_files.append(filename_abs)

    if args.all:
        for root, dirs, files in os.walk(repo_top_dir):
            # TODO(ldk): Skip '/hw/vendor' and '/hw/top_*'?
            for f in files:
                if not (f.endswith('.sv') or f.endswith('.svh')):
                    continue

                filename_abs = root + '/' + f
                if os.path.exists(filename_abs):
                    verible_files.append(filename_abs)

    logger.debug('files to format: ' + str(verible_files))

    ret = 0
    for i, f in enumerate(verible_files):
        r = process_file(f, verible_exec_path,
                         inplace=args.inplace,
                         show_diff=args.show_diff,
                         show_cst=args.show_cst)
        ret = ret + r

        if args.progress:
            print(f'\rProcessed: {i} / {len(verible_files)}\r', end='')

    if args.progress:
        print('')

    return ret > 0


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
