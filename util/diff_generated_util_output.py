#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Show a diff between the generated output from utils in the current working
tree versus a previous revision (HEAD by default). This makes it easy to
inspect the impact of modifications to either the utility implementation or
its input files on the generated output (e.g. HTML).
"""

import argparse
import os
import shlex
import subprocess
import sys
import tempfile

from reggen import version

# Test list format:
# output, outisdir, commandpre, commandpost
# if outisdir then it will be mkdired
# command is commandpre + fullpath_output + commandpost

testlist = [
    ["eguart.html", False,
     "./docgen.py docgen/examples/uart.md > ", ""],
    ["eguartcfg.html", False,
     "./docgen.py docgen/examples/uartcfg.md > ", ""],
    ["uart.html", False,
     "./docgen.py ../hw/ip/uart/doc/uart.md > ", ""],
    ["uart-d.html", False,
     "./docgen.py -d docgen/examples/uart.md > ", ""],
    ["uart16550-j.html", False,
     "./docgen.py -j docgen/examples/uart16550.md > ", ""],
    ["uart16550.html", False,
     "./docgen.py docgen/examples/uart16550.md > ", ""],
    ["regdoc.md", False,
     "./regtool.py --doc > ", ""],
    ["wave.html", False,
     "./wavetool.py wavegen/examples/* > ", ""],
    ["uart_rtl", True,
     "./regtool.py -r -t ", " ../hw/ip/uart/data/uart.hjson"],
    ["uart_dv", True,
     "./regtool.py -s -t ", " ../hw/ip/uart/data/uart.hjson"],
    # gp test multireg
    ["gp.html", False,
     "./docgen.py docgen/examples/gp.md > ", ""],
    ["gp_rtl", True,
     "./regtool.py -r -t ", " docgen/examples/gp.hjson"],
    ["gp_dv", True,
     "./regtool.py -s -t ", " docgen/examples/gp.hjson"],
    # errors tests error detection
    ["errors.html", False,
     "./docgen.py docgen/examples/errors.md > ", ""],
    # window tests
    ["window.html", False,
     "./docgen.py docgen/examples/test_win.md > ", ""],
    # include tests
    ["includes.html", False,
     "./docgen.py docgen/examples/test_inc.md > ", ""],
    # bad write enable tests
    ["badwen.html", False,
     "./docgen.py docgen/examples/badwen.md > ", ""],
    # generating include define headers
    ["uart.h", False,
     "./regtool.py -D ../hw/ip/uart/data/uart.hjson > ", ""],
    ["gpio.h", False,
     "./regtool.py -D ../hw/ip/gpio/data/gpio.hjson > ", ""],
    ["spi_device.h", False,
     "./regtool.py -D ../hw/ip/spi_device/data/spi_device.hjson > ", ""]
] # yapf: disable


def generate_output(outdir, verbose):
    for t in testlist:
        out = shlex.quote(os.path.join(outdir, t[0]))
        if t[1]:
            # in new tmpdir so the directory should never be there already
            os.mkdir(out)
        errors_out = open(out + ".STDERR", 'w', encoding='UTF-8')
        with errors_out:
            err = subprocess.call(t[2] + out + t[3],
                                  stderr=errors_out,
                                  shell=True)
            # write a file so it pops up in the diff
            # if it is different
            # (i.e. won't mention any that always return same error)
            if err != 0:
                rtn_out = open(out + ".RETURN", 'w', encoding='UTF-8')
                with rtn_out:
                    rtn_out.write("Non-Zero Return code " + str(err) + "\n")

    # useful for debug:
    if (verbose):
        subprocess.call("ls -l " + outdir, shell=True)


def main():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("treeish",
                        default="HEAD",
                        nargs="?",
                        help="git tree or commit to compare against")
    parser.add_argument('--version',
                        action='store_true',
                        help='Show version and exit')
    parser.add_argument('-v',
                        '--verbose',
                        action='store_true',
                        help='Verbose output: ls the output directories')

    args = parser.parse_args()
    if args.version:
        version.show_and_exit(__file__, [])
    args.treeish = shlex.quote(args.treeish)

    util_path = os.path.dirname(os.path.realpath(__file__))
    repo_root = os.path.abspath(os.path.join(util_path, os.pardir))
    os.chdir(repo_root)

    if not os.path.isdir(os.path.join(repo_root, '.git')):
        print("Script not in expected location in a git repo", file=sys.stderr)
        sys.exit(1)

    # Exit early if there are no diffs between the working tree and
    # args.treeish.
    output = subprocess.check_output("git diff " + args.treeish, shell=True)
    if not output:
        sys.exit(0)

    # Create temporary directories in util_path rather than defaulting to /tmp.
    # /tmp may be small and may may be mounted noexec.
    tempfile.tempdir = util_path

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_basename = os.path.basename(tmpdir)
        subprocess.check_call("git archive " + args.treeish +
                              " | tar -x -C util/" + tmpdir_basename,
                              shell=True)

        # Execute commands for working tree, saving output
        os.chdir(util_path)
        newoutdir = os.path.join(tmpdir, "newout")
        os.mkdir(newoutdir)
        generate_output(newoutdir, args.verbose)

        # Execute commands for previous revision, saving output
        os.chdir(os.path.join(tmpdir_basename, "util"))
        oldoutdir = os.path.join(tmpdir, "oldout")
        os.mkdir(oldoutdir)
        generate_output(oldoutdir, args.verbose)

        # Show diff (if any)
        os.chdir(tmpdir)
        # Don't use a checked call because the exit code indicates whether there
        # is a diff or not, rather than indicating error.
        subprocess.call('git diff -p --stat --no-index oldout newout',
                        shell=True)


if __name__ == "__main__":
    main()
