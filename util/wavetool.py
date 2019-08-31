#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to convert wavejson to svg
"""

import argparse
import logging as log
import sys

import hjson
import pkg_resources  # part of setuptools

from reggen import version
from wavegen import wavesvg

USAGE = """
  wavetool [options]
  wavetool [options] <input> [<input>]...
"""

wavejson = """
{signal: [
  {name:'Baud Clock',  wave: 'p...........' },
  {name:'Data 8 bit',        wave: '10========1=',
   data: [ "lsb", "", "", "", "", "", "", "msb", "next" ] },
  {name:'Data 7 bit',        wave: '10=======1=.',
   data: [ "lsb", "", "", "", "", "", "msb", "next" ] },
  {name:'Data 6 bit',        wave: '10======1=..',
   data: [ "lsb", "", "", "", "", "msb", "next" ] },
  {name:'5 bit,halfbaud',        wave: '10=====1=.|.', period:2,
   data: [ "lsb", "", "", "", "msb", "next" ] },
  {},
  {name:'8 with Parity', wave: '10=========1',
   data: [ "lsb", "", "", "", "", "", "", "msb", "par" ] },
  {name:'10udz1xHL', wave: '10udz1xHL' },
  {name:'5 bit,cdata',        wave: '10=====1=...',
   cdata: [ "idle", "start", "lsb", "", "", "", "msb", "stop", "next" ] },
 ],
 head:{
   text:'Serial Line format (one stop bit)',
   tock:-1,
 }
}

"""


def main():
    done_stdin = False
    parser = argparse.ArgumentParser(
        prog="wavetool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE,
        description=__doc__,
        epilog='defaults or the filename - can be used for stdin/stdout')
    parser.add_argument(
        '--version', action='store_true', help='Show version and exit')
    parser.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        help='Verbose output during processing')
    parser.add_argument(
        '-T',
        '--testmode',
        action='store_true',
        help='Run test with built-in source')
    parser.add_argument(
        '-o',
        '--output',
        type=argparse.FileType('w'),
        default=sys.stdout,
        metavar='file',
        help='Output file (default stdout)')
    parser.add_argument(
        'srcfile',
        nargs='*',
        metavar='input',
        default='-',
        help='source wavejson file (default stdin)')
    args = parser.parse_args()

    if args.version:
        version.show_and_exit(__file__, ["Hjson"])

    if (args.verbose):
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    outfile = args.output

    with outfile:
        if args.testmode:
            obj = hjson.loads(wavejson)

            svg0 = wavesvg.convert(obj, 0)
            svg1 = wavesvg.convert(obj, 1)
            outfile.write(svg0)
            outfile.write('<h2>Generate again, should not repeat defs</h2>\n')
            outfile.write(svg1)
        else:
            num = 0
            for filename in args.srcfile:
                if (filename == '-'):
                    if (done_stdin):
                        log.warn("Ignore stdin after first use\n")
                        continue
                    done_stdin = True
                    infile = sys.stdin
                else:
                    infile = open(filename, 'r', encoding='UTF-8')
                with infile:
                    obj = hjson.load(infile)
                    log.info("\nFile now " + filename)
                    outfile.write("<H2>" + filename + "</H2>")
                    outfile.write(wavesvg.convert(obj, num))
                    num += 1


if __name__ == '__main__':
    main()
