"""
This script lint the various opentitan testplan.hjson
usage:
    python3 ./util/lint_testplan.py --rules hw/lint/sival_testplan_rules.json --dir hw/top_earlgrey/data/ip/
"""

import argparse
import difflib
import glob
import json
import logging
import sys
import re

import hjson

LOWRISC_HEADER = """// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
"""

parser = argparse.ArgumentParser()
parser.add_argument(
    "--logging",
    default="info",
    choices=["debug", "info", "warning", "error", "critical"],
    help="Logging level",
)
parser.add_argument(
    "--dir",
    required=True,
    help="A dir with all the testplan.hjson.",
)
parser.add_argument(
    "--formatting-check",
    action=argparse.BooleanOptionalAction,
    help="Check the formatting.",
)
parser.add_argument(
    "--formatting-fix",
    action=argparse.BooleanOptionalAction,
    help="Check the formatting.",
)


def main(args) -> int:
    if not (args.formatting_check or args.formatting_fix):
        args.print_help(sys.stderr)
        return -1

    files = [f for f in glob.glob(f"{args.dir}/*.hjson")]

    if args.formatting_fix:
        Formatting().check(files, True)
    elif args.formatting_check:
        return Formatting().check(files)
    return 0


class CustomEncoder(hjson.HjsonEncoder):
    level = 0
    newline = '\n'
     # Strings inside lists must have double quotes.
    is_list_of_dict = True
    current_key = ""
    def encode(self, obj):
        if isinstance(obj, dict):
            if self.level > 0:
                yield f'{self.newline}{self.indent*self.level}'
            yield '{'
            self.level +=1
            self.is_list_of_dict = True
            for key, value in obj.items():
                self.current_key = key
                yield f'{self.newline}{self.indent*self.level}{key}: '
                yield from self.encode(value)
            self.level -= 1
            yield f'{self.newline}{self.indent*self.level}}}'
        elif isinstance(obj, list):
            self.level +=1
            yield '['
            self.is_list_of_dict = False
            for (enum,item) in enumerate(obj):
                yield from self.encode(item)
                if not self.is_list_of_dict and enum < len(obj)-1:
                    yield ', '
            self.level -=1
            if self.is_list_of_dict:
                yield f'{self.newline}{self.indent*self.level}'
            yield ']'
            self.is_list_of_dict = True
        elif isinstance(obj, str):
            if f'{self.newline}' in obj:
                yield self.multiline_str(obj)
            else:
                yield f'{obj}' if self.is_list_of_dict else f'"{obj}"'
        else:
            yield str(obj)

    def multiline_str(self, text):
        align = len(self.current_key) + 2
        indented = f'{self.newline}' + text + f'{self.newline}'
        # Add indentation
        indented = indented.replace(f'{self.newline}', f'{self.newline}{self.indent*(self.level)}{" "*align}')
        # Remove indentation from empty lines
        indented = re.sub(f'{self.newline}{self.indent}+{self.newline}', f'{self.newline}\n', indented)
        return f"'''{indented}'''"
        
    def iterencode(	self, obj, _one_shot=False):
        for chunk in self.encode(obj):
            yield chunk

class Formatting:
    def check(self, files, fix=False) -> int:
        WORK_FILE = "/tmp/linter_test.hjson"
        for filename in files:
            testplan = hjson.load(open(filename, "r"))
            logging.debug(f"Checking {filename}.")
            self.__dump_to_file(WORK_FILE, testplan)
            try:
                self.__diff_files(WORK_FILE, filename)
            except TestplanLintException as e:
                if fix:
                    logging.info(f"Fixing file {filename}.")
                    self.__dump_to_file(filename, testplan)
                    continue

                logging.info(f"Error found in file {filename}: {e}")
                return -1
        return 0

    def __dump_to_file(self, filename, testplan):
        with open(filename, "w") as f:
            f.write(LOWRISC_HEADER)
            hjson.dump(testplan, f, cls=CustomEncoder, indent="  ")
            f.write("\n")

    def __diff_files(self, ref_file, file):
        text = open(file, "r").readlines()
        ref_text = open(ref_file, "r").readlines()
        diff = difflib.unified_diff(
            text, ref_text, fromfile=file, tofile=ref_file, lineterm="\n"
        )
        msg = "".join(diff)

        if len(msg) > 0:
            raise TestplanLintException("\n" + msg)

class TestplanLintException(Exception):
    pass


if __name__ == "__main__":
    args = parser.parse_args()
    logging.basicConfig(level=args.logging.upper())
    sys.exit(main(args))
