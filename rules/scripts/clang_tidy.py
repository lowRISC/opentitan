#!/usr/bin/env python3
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This wrapper script acts as a shim between Bazel and clang-tidy.
"""

import argparse
import fcntl
from pathlib import Path
import subprocess
import sys
import time


def maybe_rename_path(orig: Path, new: Path):
    """Tries to rename `orig` to `new`. Returns an "undo" lambda.
    """
    try:
        orig.rename(new)
    except FileNotFoundError:
        pass
    return lambda: maybe_rename_path(new, orig)


def acquire_lock(path: Path):
    """Blocks until acquiring an exclusive lock on `path`.
    """
    with open(path, "a+") as f:
        while True:
            try:
                fcntl.flock(f, fcntl.LOCK_EX)
                return
            except IOError:
                time.sleep(0.1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--ignore-clang-tidy-error', action='store_true')
    parser.add_argument('--print-args', action='store_true')
    parser.add_argument('lock_file', type=Path)
    parser.add_argument('out_file', type=Path)
    parser.add_argument('clang_tidy')
    parser.add_argument('clang_tidy_args', nargs=argparse.REMAINDER)

    args = parser.parse_args()

    if args.print_args:
        print("Args that will be passed to clang-tidy:")
        for arg in args.clang_tidy_args:
            print(" ", arg)

    # Acquire an exclusive lock before proceeding. There are two reasons for locking.
    #
    # (1) We need to ensure that the compilation database is not present when
    #     clang-tidy runs. If compile_commands.json exists, clang-tidy will read
    #     it and ignore the compiler arguments we give it. There does not appear
    #     to be a command-line flag that controls this behavior, so all we can
    #     do is ensure the file isn't present when clang-tidy runs.
    #
    # (2) Without locking, headers may receive the same fix multiple times. For
    #     instance, strict prototype fixes might pile up on `void Foo();` to
    #     create something like `void Foo(voidvoidvoid);`. This happens because
    #     Bazel runs many instances of clang-tidy in parallel, and clang-tidy
    #     has no synchronization mechanism.
    #
    # To run clang-tidy in parallel without locking, we would need to export
    # fixes and deduplicate before applying them. Unfortunately, we cannot apply
    # the fixes that `--export-fixes` creates because our toolchain doesn't
    # include the `clang-apply-replacements` binary.
    acquire_lock(args.lock_file)

    compile_commands = Path("compile_commands.json")
    cleanup_func = maybe_rename_path(
        compile_commands, compile_commands.with_suffix(".tmp-clang-tidy"))

    assert not compile_commands.exists()

    clang_tidy_command = [args.clang_tidy] + args.clang_tidy_args
    proc = subprocess.run(clang_tidy_command)
    if proc.returncode != 0:
        print(f"clang-tidy exited with {proc.returncode}")

        if not args.ignore_clang_tidy_error:
            cleanup_func()
            return proc.returncode

    args.out_file.touch()

    cleanup_func()
    return 0


if __name__ == '__main__':
    sys.exit(main())
