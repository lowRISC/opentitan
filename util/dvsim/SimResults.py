# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing simulation results
"""

import collections
import re
from testplanner.class_defs import TestResult


_REGEX_REMOVE = [
    # Remove UVM time.
    re.compile(r'@\s+[\d.]+\s+[np]s: '),
    re.compile(r'\[[\d.]+\s+[np]s\] '),
    # Remove assertion time.
    re.compile(r'\(time [\d.]+ [PF]S\) '),
    # Remove leading spaces.
    re.compile(r'^\s+'),
    # Remove extra white spaces.
    re.compile(r'\s+(?=\s)'),
]

_REGEX_STRIP = [
    # Strip TB instance name.
    re.compile(r'[\w_]*top\.\S+\.(\w+)'),
    # Strip assertion.
    re.compile(r'(?<=Assertion )\S+\.(\w+)'),
]

# Regular expression for a separator: EOL or some of punctuation marks.
_SEPARATOR_RE = '($|[ ,.:;])'

_REGEX_STAR = [
    # Replace hex numbers with 0x (needs to be called before other numbers).
    re.compile(r'0x\s*[\da-fA-F]+'),
    # Replace hex numbers with 'h (needs to be called before other numbers).
    re.compile(r'\'h\s*[\da-fA-F]+'),
    # Floating point numbers at the beginning of a word, example "10.1ns".
    # (needs to be called before other numbers).
    re.compile(r'(?<=[^a-zA-Z0-9])\d+\.\d+'),
    # Replace all isolated numbers. Isolated numbers are numbers surrounded by
    # special symbols, for example ':' or '+' or '_', excluding parenthesis.
    # So a number with a letter or a round bracket on any one side, is
    # considered non-isolated number and is not starred by these expressions.
    re.compile(r'(?<=[^a-zA-Z0-9\(\)])\d+(?=($|[^a-zA-Z0-9\(\)]))'),
    # Replace numbers surrounded by parenthesis after a space and followed by a
    # separator.
    re.compile(r'(?<= \()\s*\d+\s*(?=\)%s)' % _SEPARATOR_RE),
    # Replace hex/decimal numbers after an equal sign or a semicolon and
    # followed by a separator. Uses look-behind pattern which need a
    # fixed width, thus the apparent redundancy.
    re.compile(r'(?<=[\w\]][=:])[\da-fA-F]+(?=%s)' % _SEPARATOR_RE),
    re.compile(r'(?<=[\w\]][=:] )[\da-fA-F]+(?=%s)' % _SEPARATOR_RE),
    re.compile(r'(?<=[\w\]] [=:])[\da-fA-F]+(?=%s)' % _SEPARATOR_RE),
    re.compile(r'(?<=[\w\]] [=:] )[\da-fA-F]+(?=%s)' % _SEPARATOR_RE),
    # Replace decimal number at the beginning of the word.
    re.compile(r'(?<= )\d+(?=\S)'),
    # Remove decimal number at end of the word and before '=' or '[' or
    # ',' or '.' or '('.
    re.compile(r'(?<=\S)\d+(?=($|[ =\[,\.\(]))'),
    # Replace the instance string.
    re.compile(r'(?<=instance)\s*=\s*\S+'),
]


class SimResults:
    '''An object wrapping up a table of results for some tests

    self.table is a list of TestResult objects, each of which
    corresponds to one or more runs of the test with a given name.

    self.buckets contains a dictionary accessed by the failure signature,
    holding all failing tests with the same signature.
    '''

    def __init__(self, items, results):
        self.table = []
        self.buckets = collections.defaultdict(list)
        self._name_to_row = {}
        for item in items:
            self._add_item(item, results)

    def _add_item(self, item, results):
        '''Recursively add a single item to the table of results'''
        status = results[item]
        if status == "F":
            bucket = self._bucketize(item.launcher.fail_msg.message)
            self.buckets[bucket].append(
                (item, item.launcher.fail_msg.line_number,
                 item.launcher.fail_msg.context))

        # Runs get added to the table directly
        if item.target == "run":
            self._add_run(item, status)

    def _add_run(self, item, status):
        '''Add an entry to table for item'''
        row = self._name_to_row.get(item.name)
        if row is None:
            row = TestResult(item.name)
            self.table.append(row)
            self._name_to_row[item.name] = row

        if status == 'P':
            row.passing += 1
        row.total += 1

    def _bucketize(self, fail_msg):
        bucket = fail_msg
        # Remove stuff.
        for regex in _REGEX_REMOVE:
            bucket = regex.sub('', bucket)
        # Strip stuff.
        for regex in _REGEX_STRIP:
            bucket = regex.sub(r'\g<1>', bucket)
        # Replace with '*'.
        for regex in _REGEX_STAR:
            bucket = regex.sub('*', bucket)
        return bucket
