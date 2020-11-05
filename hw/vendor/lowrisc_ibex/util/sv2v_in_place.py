#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import logging
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from typing import List, Pattern, Tuple


def read_file_list(path: str) -> List[str]:
    '''Read in a list of paths from a file, one per line.'''
    ret = []
    with open(path) as handle:
        for line in handle:
            ret.append(line.strip())
    return ret


def transform_one(sv2v: str,
                  defines: List[str],
                  incdirs: List[str],
                  pkg_paths: List[str],
                  sv_path: str,
                  dst_path: str) -> None:
    '''Run sv2v to edit a file in place'''
    defines_args = ['--define=' + d for d in defines]
    incdirs_args = ['--incdir=' + d for d in incdirs]
    paths = pkg_paths + ([] if sv_path in pkg_paths else [sv_path])

    cmd = ([sv2v,
            # Pass --exclude=assert to tell sv2v not to strip out assertions.
            # Since the whole point of this flow is to prove assertions, we
            # need to leave them unscathed!
            '--exclude=assert'] +
           defines_args +
           incdirs_args +
           paths)
    logging.info('Running sv2v on {}'.format(sv_path))
    logging.debug('Command: {}'.format(cmd))
    with open(dst_path, 'w') as dst_file:
        proc = subprocess.run(cmd, stdout=dst_file)
        if proc.returncode != 0:
            cmd_str = ' '.join([shlex.quote(a) for a in cmd])
            raise RuntimeError('Failed to run sv2v on {}. '
                               'Exit code: {}. Full command: {}'
                               .format(sv_path, proc.returncode, cmd_str))


def parse_define_if(arg: str) -> Tuple[Pattern[str], str]:
    '''Handle a --define-if argument'''
    parts = arg.rsplit(':', 1)
    if len(parts) != 2:
        msg = ('The --define-if argument {!r} contains no colon. The correct '
               'syntax is "--define-if regex:define".'
               .format(arg))
        raise argparse.ArgumentTypeError(msg)

    re_str, define = parts
    try:
        return (re.compile(re_str), define)
    except re.error as err:
        raise argparse.ArgumentTypeError('The regex for the --define-if '
                                         'argument ({!r}) is malformed: {}.'
                                         .format(re_str, err))


def transform(sv2v: str,
              defines: List[str],
              defines_if: List[Tuple[Pattern[str], str]],
              incdirs: List[str],
              pkg_paths: List[str],
              sv_paths: List[str]) -> None:
    '''Run sv2v to transform a list of files in-place'''
    with tempfile.TemporaryDirectory() as tmpdir:
        # First write each file to a file in a temporary directory, then copy
        # everything back. We have to do it like this because otherwise we
        # might trash a file that needs to be included by a later one.
        dst_paths = []
        for idx, src_path in enumerate(sv_paths):
            dst_path = os.path.join(tmpdir, str(idx))

            extra_file_defines = []
            for regex, define in defines_if:
                if regex.search(src_path):
                    extra_file_defines.append(define)

            transform_one(sv2v, defines + extra_file_defines,
                          incdirs, pkg_paths, src_path, dst_path)
            dst_paths.append(dst_path)

        # Now copy everything back, overwriting the original code
        for dst_path, src_path in zip(dst_paths, sv_paths):
            shutil.copy(dst_path, src_path)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('file_list',
                        help=('File containing a list of '
                              'paths on which to work.'))
    parser.add_argument('--verbose', '-v', action='store_true',
                        help="Log messages about what we're doing.")
    parser.add_argument('--define', '-D', action='append', dest='defines',
                        default=[],
                        help='Add a preprocessor define.')
    parser.add_argument('--define-if', action='append',
                        dest='defines_if', type=parse_define_if, default=[],
                        help=('Add a preprocessor define which applies to '
                              'specific files. For example '
                              '--define-if=foo:bar would define `bar on any '
                              'files whose paths contained a match for the '
                              'regex "foo".'))
    parser.add_argument('--incdir', '-I', action='append', dest='incdirs',
                        default=[],
                        help='Add an include dir for the preprocessor.')
    parser.add_argument('--incdir-list',
                        help=('Specify a file containing a list of include '
                              'directories (which are appended to any defined '
                              'through the --incdir argument).'))
    parser.add_argument('--sv2v',
                        default='sv2v',
                        help=("Specify the name or path of the sv2v binary. "
                              "Defaults to 'sv2v'."))

    args = parser.parse_args()

    if args.verbose:
        logging.basicConfig(level=logging.INFO)

    try:
        logging.info('Reading file list from {!r}.'.format(args.file_list))
        paths = read_file_list(args.file_list)
    except IOError:
        logging.error('Failed to read file list from {!r}'
                      .format(args.file_list))
        return 1

    if args.incdir_list is not None:
        try:
            logging.info('Reading incdir list from {!r}.'
                         .format(args.incdir_list))
            args.incdirs += read_file_list(args.incdir_list)
        except IOError:
            logging.error('Failed to read incdir list from {!r}'
                          .format(args.file_list))
            return 1

    # Find all .sv or .svh files, splitting out paths ending in "pkg.sv"
    # specially. We treat these as packages, which are included in each sv2v
    # conversion.
    sv_paths = []
    svh_paths = []
    pkg_paths = []
    for path in paths:
        if os.path.splitext(path)[1] == '.sv':
            sv_paths.append(path)
        if os.path.splitext(path)[1] == '.svh':
            svh_paths.append(path)
        if path.endswith('pkg.sv'):
            pkg_paths.append(path)

    logging.info('Running sv2v in-place on {} files ({} packages).'
                 .format(len(sv_paths), len(pkg_paths)))

    try:
        transform(args.sv2v, args.defines, args.defines_if, args.incdirs,
                  pkg_paths, sv_paths)
    except RuntimeError as err:
        logging.error(err)
        return 1

    # Empty out any remaining .svh files: they should have been included by
    # this point (sv2v includes a preprocessor).
    logging.info('Splatting contents of {} .svh files.'.format(len(svh_paths)))
    for path in svh_paths:
        with open(path, 'w'):
            pass

    return 0


if __name__ == '__main__':
    exit(main())
