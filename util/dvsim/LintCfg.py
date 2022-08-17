# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r'''
Class describing lint configuration object
'''

import logging as log
from pathlib import Path

from tabulate import tabulate

from OneShotCfg import OneShotCfg
from utils import subst_wildcards, check_bool
from MsgBuckets import MsgBuckets


class LintCfg(OneShotCfg):
    '''Derivative class for linting purposes.'''

    flow = 'lint'

    def __init__(self, flow_cfg_file, hjson_data, args, mk_config):
        # TODO: check whether this can be replaced with the subflow concept.
        # This determines whether the flow is for a style lint run.
        # Format: bool
        self.is_style_lint = ''
        # Determines which message severities to print into report summaries
        # Format: [str, ...]
        self.report_severities = []
        # Determines which message severities lead to a pass/fail
        # Format: [str, ...]
        self.fail_severities = []
        # Message bucket format configuration
        # Format: [{category: str, severity: str,  label: str}, ...]
        self.message_buckets = []

        super().__init__(flow_cfg_file, hjson_data, args, mk_config)

        if self.is_style_lint == '':
            self.is_style_lint = False
        else:
            self.is_style_lint = check_bool(self.is_style_lint)

        # Set the title for lint results.
        if self.is_style_lint:
            self.results_title = f'{self.name.upper()} Style Lint Results'
        else:
            self.results_title = f'{self.name.upper()} Lint Results'

    def gen_results_summary(self):
        '''
        Gathers the aggregated results from all sub configs
        '''

        # Generate results table for runs.
        log.info('Create summary of lint results')

        results_str = f'## {self.results_title} (Summary)\n\n'
        results_str += f'### {self.timestamp_long}\n'
        if self.revision:
            results_str += f'### {self.revision}\n'
        results_str += f'### Branch: {self.branch}\n'
        results_str += '\n'

        # Aggregate with all summaries
        self.totals = MsgBuckets(self.message_buckets)
        for cfg in self.cfgs:
            self.totals += cfg.result_summary

        # Construct Header
        labels = self.totals.get_labels(self.report_severities)
        header = ['Name'] + labels
        colalign = ('center', ) * len(header)
        table = [header]

        keys = self.totals.get_keys(self.report_severities)
        for cfg in self.cfgs:
            name_with_link = cfg._get_results_page_link(
                self.results_dir)

            row = [name_with_link]
            row += cfg.result_summary.get_counts_md(keys)
            table.append(row)

        if len(table) > 1:
            self.results_summary_md = results_str + tabulate(
                table, headers='firstrow', tablefmt='pipe',
                colalign=colalign) + '\n'
        else:
            self.results_summary_md = f'{results_str}\nNo results to display.\n'

        print(self.results_summary_md)

        # Return only the tables
        return self.results_summary_md

    # TODO(#9079): This way of parsing out messages into an intermediate
    # results.hjson file will be replaced by a native parser mechanism.
    def _gen_results(self, results):
        # '''
        # The function is called after the regression has completed. It looks
        # for a results.hjson file with aggregated results from the lint run.
        # The hjson needs to have the following format:
        #
        # {
        #     bucket_key: [str],
        #     // other buckets according to message_buckets configuration
        # }
        #
        # Each bucket key points to a list of signatures (strings).
        # The bucket categories and severities are defined in the
        # message_buckets class variable, and can be set via Hjson Dvsim
        # config files.
        #
        # Note that if this is a primary config, the results will
        # be generated using the _gen_results_summary function
        # '''

        # Generate results table for runs.
        results_str = f'## {self.results_title}\n\n'
        results_str += f'### {self.timestamp_long}\n'
        if self.revision:
            results_str += f'### {self.revision}\n'
        results_str += f'### Branch: {self.branch}\n'
        results_str += f'### Tool: {self.tool.upper()}\n\n'

        # Load all result files from all build modes and convert them to
        # message buckets.
        self.result = []
        self.result_summary = MsgBuckets(self.message_buckets)
        for mode in self.build_modes:
            result_path = Path(
                subst_wildcards(self.build_dir, {'build_mode': mode.name}) +
                '/results.hjson')
            log.info('[results:hjson]: [%s]: [%s]', self.name, result_path)
            # TODO(#9079): replace this with native log parser
            msgs = MsgBuckets(self.message_buckets)
            msgs.load_hjson(result_path)
            self.result.append(msgs)
            # Aggregate with summary results
            self.result_summary += msgs

        # Construct Header
        labels = self.result_summary.get_labels(self.report_severities)
        header = ['Build Mode'] + labels
        colalign = ('center', ) * len(header)
        table = [header]
        fail_msgs = ''
        self.errors_seen = 0
        keys = self.result_summary.get_keys(self.report_severities)
        for mode, res in zip(self.build_modes, self.result):
            row = [mode.name] + res.get_counts_md(keys)
            table.append(row)
            self.errors_seen += res.has_signatures(self.fail_severities)
            fail_msgs += f"\n### Messages for Build Mode `'{mode.name}'`\n"
            fail_msgs += res.print_signatures_md(self.report_severities,
                                                 self.max_msg_count)

        if len(table) > 1:
            self.results_md = results_str + tabulate(
                table, headers='firstrow', tablefmt='pipe',
                colalign=colalign) + '\n'

            # Th published report will default to self.results_md if they are
            # empty. In case it needs need to be sanitized, override it and do
            # not append detailed messages.
            if self.sanitize_publish_results:
                self.publish_results_md = self.results_md
            # Locally generated result always contains all details.
            self.results_md += fail_msgs
        else:
            self.results_md = f'{results_str}\nNo results to display.\n'
            self.publish_results_md = self.results_md

        return self.results_md
