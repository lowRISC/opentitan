#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


class CheckResult:
    '''A class to record the results of static checks.

    Can record any number of errors and warnings. Combine two check results
    with +, e.g.:

        out = CheckResult()
        out += first_check()
        out += second_check()
        out.warn('A warning')
        print(out.report()) # prints warnings/errors from both checks and "A warning"
    '''
    def __init__(self):
        self.errors = []
        self.warnings = []
        self.prefix = ''

    def warn(self, msg):
        '''Add a warning.'''
        self.warnings.append(msg)

    def err(self, msg):
        '''Add an error.'''
        self.errors.append(msg)

    def __add__(self, other):
        '''Combines both operands' errors/warnings in a new CheckResult.'''
        if not isinstance(other, CheckResult):
            raise ValueError(
                'Cannot add {} (of type {}) to {} (of type CheckResult)'.
                format(other, type(other), self))
        out = CheckResult()
        out.warnings = self.warnings + other.warnings
        out.errors = self.errors + other.errors
        return out

    def set_prefix(self, prefix):
        '''Add a prefix to the printouts for this check.'''
        self.prefix = prefix

    def has_errors(self):
        return len(self.errors) != 0

    def has_warnings(self):
        return len(self.warnings) != 0

    def report(self):
        '''Show a message to represent the results of the check.'''
        if not self.has_warnings() and not self.has_errors():
            return '{}PASS'.format(self.prefix)
        warn_strs = [
            '{}WARN: {}'.format(self.prefix, w) for w in self.warnings
        ]
        err_strs = ['{}ERROR: {}'.format(self.prefix, e) for e in self.errors]
        return '\n'.join(warn_strs + err_strs)
