# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''
This class holds a dict of message buckets according to the format defined
upon construction. It is meant to hold all message buckets of a build / tool
run, and provides convenience functions that streamline result aggregation
and printout in the Dvsim flow classes.
'''

import hjson
import copy
import logging as log

from pathlib import Path
from typing import Dict, List
from utils import print_msg_list
from MsgBucket import MsgBucket


class MsgBuckets():
    def __init__(self,
                 bucket_cfgs: List[Dict]) -> None:
        self.buckets = {f"{b['category']}_{b['severity']}":
                        MsgBucket(b['category'], b['severity'], b['label'])
                        for b in bucket_cfgs}

    def clear(self):
        '''Clear all signatures in all buckets'''
        for b in self.buckets.values():
            b.clear()

    def get_labels(self,
                   severity_filter: List[str] = []) -> List[str]:
        '''
        Returns all bucket labels as a list.

        If severity_filter is not empty, only the buckets with the listed
        severities will be returned.
        '''
        for s in severity_filter:
            if not MsgBucket.severity_is_known(s):
                RuntimeError(f'Unknown severity {s}')

        labels = []
        for key, b in self.buckets.items():
            if not severity_filter or b.severity in severity_filter:
                labels.append(b.label)
        return labels

    def get_keys(self,
                 severity_filter: List[str] = []) -> List[str]:
        '''
        Returns all bucket keys as a list.

        If severity_filter is not empty, only the buckets with the listed
        severities will be returned.
        '''
        for s in severity_filter:
            if not MsgBucket.severity_is_known(s):
                RuntimeError(f'Unknown severity {s}')

        keys = []
        for key, b in self.buckets.items():
            if not severity_filter or b.severity in severity_filter:
                keys.append(key)
        return keys

    def get_counts(self,
                   keys: List[str] = None,
                   severity_filter: List[str] = []) -> List[int]:
        '''
        Get bucket count totals as a list of integers.

        The bucket keys can be supplied externally, in which case the
        severity_filter does not apply. If a specific bucket key does not
        exist, a 0 count will be returned for that specific key.

        If severity_filter is not empty, only the buckets with the listed
        severities will be returned.
        '''
        if not keys:
            keys = self.get_keys(severity_filter)
        counts = []
        for k in keys:
            c = self.buckets[k].count() if k in self.buckets else 0
            counts.append(c)
        return counts

    def get_counts_md(self,
                      keys: List[str] = None,
                      severity_filter: List[str] = [],
                      colmap: bool = True) -> List[str]:
        '''
        Get bucket count totals as a list of strings with optional colormap.

        The bucket keys can be supplied externally, in which case the
        severity_filter does not apply. If a specific bucket key does not
        exist, a "--" string will be returned for that specific key.

        If severity_filter is not empty, only the buckets with the listed
        severities will be returned.
        '''
        if not keys:
            keys = self.get_keys(severity_filter)
        counts = []
        for k in keys:
            c = self.buckets[k].count_md(colmap) if k in self.buckets else '--'
            counts.append(c)
        return counts

    def has_signatures(self,
                       severity_filter: List[str] = []) -> bool:
        '''
        Checks whether there are any signatures with specified severities.

        If severity_filter is empty, the method returns true if any of the
        buckets contains a nonzero amount of signatures.

        '''
        return any(self.get_counts(severity_filter=severity_filter))

    def print_signatures_md(self,
                            severity_filter: List[str] = [],
                            max_per_bucket: int = -1) -> str:
        '''
        Render signatures into a string buffer.

        The bucket labels are used as subtitles in this printout.

        If severity_filter is not empty, only the buckets with the listed
        severities will be returned.

        The number of messages printed per bucket can be limited by
        setting max_per_bucket to a nonnegative value.
        '''
        msgs = ''
        keys = self.get_keys(severity_filter)

        for k in keys:
            msgs += print_msg_list(f'#### {self.buckets[k].label}',
                                   self.buckets[k].signatures,
                                   max_per_bucket)
        return msgs

    def merge(self, other) -> None:
        '''
        Merge other MsgBuckets object into this one.

        This will append signatures to the corresponding bucket if it exists.
        If the bucket does not yet exist it will be created.
        '''

        for k, b in other.buckets.items():
            if k in self.buckets:
                self.buckets[k].merge(b)
            else:
                self.buckets.update({k: copy.deepcopy(b)})

    def __add__(self, other):
        '''
        Merges two MsgBucket objects into one.

        Buckets will be uniquified, and signatures in buckets with the same
        category and severity will be merged.
        '''
        mb = copy.deepcopy(self)
        mb.merge(other)
        return mb

    # TODO(#9079): remove the method below once the log parsing has been
    # merged into the Dvsim core code.
    def load_hjson(self, result_path: Path) -> None:
        '''Clear internal data structure and initialize with values in Hjson'''
        self.clear()
        try:
            with result_path.open() as results_file:
                results_dict = hjson.load(results_file, use_decimal=True)
        except IOError as err:
            log.warning("%s", err)
            if 'flow_error' not in self.buckets:
                self.buckets.update({'flow_error': MsgBucket('flow',
                                                             'error')})
            self.buckets['flow_error'].signatures.append('IOError: %s' % err)
            return

        for k, signatures in results_dict.items():
            if not isinstance(signatures, List):
                raise RuntimeError(f'Signatures in {k} must be a '
                                   'list of strings')
            self.buckets[k].signatures.extend(signatures)
