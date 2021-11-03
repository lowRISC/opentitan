# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''
Class describing lint configuration object
'''

import logging as log
from pathlib import Path

from tabulate import tabulate

from LintCfg import LintCfg
from utils import subst_wildcards, check_bool
from MsgBuckets import MsgBuckets


class CdcCfg(LintCfg):
    '''Derivative class for linting purposes.'''

    flow = 'cdc'

    def __init__(self, flow_cfg_file, hjson_data, args, mk_config):
        super().__init__(flow_cfg_file, hjson_data, args, mk_config)

        self.results_title = f'{self.name.upper()} CDC Results'
