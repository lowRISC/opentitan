# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''
RDC Configuration Class
'''

from LintCfg import LintCfg


class RdcCfg(LintCfg):
    '''Reset Domain Crossing'''

    flow = 'rdc'

    def __init__(self, flow_cfg_file, hjson_data, args, mk_config):

        super().__init__(flow_cfg_file, hjson_data, args, mk_config)

        self.results_title = f'{self.name.upper()} RDC Results'
