# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''
Message bucket class that encapsulates information such as bucket
category, bucket severity, the associated label for the results table, and
a list with message signatures.
'''

import copy


class MsgBucket():

    # Known severity levels and color map for Dvsim summary tables.
    SEVERITIES = {
        'info': 'I',
        'review': 'W',
        'warning': 'W',
        'error': 'E',
        'fatal': 'E'
    }

    @classmethod
    def severity_is_known(cls, severity: str) -> bool:
        '''Returns true if the severity is known'''
        return severity in cls.SEVERITIES

    def __init__(self,
                 category: str,
                 severity: str,
                 label: str = None) -> None:
        if not MsgBucket.severity_is_known(severity):
            RuntimeError(f'Unknown severity {severity}')
        self.category = category
        self.severity = severity
        self.label = f'{category} {severity}s'.title() if not label else label
        self.signatures = []

    def clear(self) -> None:
        '''Clears the signatures list'''
        self.signatures = []

    def count(self) -> int:
        '''Return number of signatures'''
        return len(self.signatures)

    def count_md(self, colmap: bool = True) -> str:
        '''Return count string with optional colormap applied'''
        countstr = str(self.count())
        if colmap:
            countstr += ' ' + self.SEVERITIES[self.severity]
        return countstr

    def merge(self, other) -> None:
        '''Merge other bucket into this one'''

        if self.category != other.category:
            raise RuntimeError(f'Category {other.category} does not match '
                               f'{self.category} for bucket {self.label}')

        elif self.severity != other.severity:
            raise RuntimeError(f'Severity {other.severity} does not match '
                               f'{self.severity} for bucket {self.label}')
        else:
            self.signatures.extend(copy.deepcopy(other.signatures))

    def __add__(self, other):
        '''Merges two message buckets into one'''
        mb = copy.deepcopy(self)
        mb.merge(other)
        return mb
