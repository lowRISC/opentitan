# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing lint configuration object
"""

import hjson
import logging as log
from pathlib import Path

from tabulate import tabulate

from OneShotCfg import OneShotCfg
from utils import print_msg_list, subst_wildcards


class LintCfg(OneShotCfg):
    """Derivative class for linting purposes.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        # This is a lint-specific attribute
        self.is_style_lint = ""
        super().__init__(flow_cfg_file, proj_root, args)

    def __post_init__(self):
        super().__post_init__()

        # Convert to boolean
        if self.is_style_lint == "True":
            self.is_style_lint = True
        else:
            self.is_style_lint = False

        # Set the title for lint results.
        if self.is_style_lint:
            self.results_title = self.name.upper() + " Style Lint Results"
        else:
            self.results_title = self.name.upper() + " Lint Results"

    def gen_results_summary(self):
        '''
        Gathers the aggregated results from all sub configs
        '''

        # Generate results table for runs.
        log.info("Create summary of lint results")

        results_str = "## " + self.results_title + " (Summary)\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        if self.revision_string:
            results_str += "### " + self.revision_string + "\n"
        results_str += "\n"


        header = [
            "Name", "Tool Warnings", "Tool Errors", "Lint Warnings",
            "Lint Errors"
        ]
        colalign = ("center", ) * len(header)
        table = [header]

        for cfg in self.cfgs:

            results_page = cfg.results_server_dir + '/results.html'
            results_page_url = results_page.replace(
                cfg.results_server_prefix, cfg.results_server_url_prefix)
            name_with_link = "[" + cfg.name.upper(
            ) + "](" + results_page_url + ")"
            table.append([
                name_with_link,
                str(len(cfg.result_summary["warnings"])) + " W",
                str(len(cfg.result_summary["errors"])) + " E",
                str(len(cfg.result_summary["lint_warnings"])) + " W",
                str(len(cfg.result_summary["lint_errors"])) + " E"
            ])

        if len(table) > 1:
            self.results_summary_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe",
                colalign=colalign) + "\n"
        else:
            self.results_summary_md = results_str + "\nNo results to display.\n"

        print(self.results_summary_md)

        # Return only the tables
        return self.results_summary_md

    def _gen_results(self):
        # '''
        # The function is called after the regression has completed. It looks
        # for a regr_results.hjson file with aggregated results from the lint run.
        # The hjson needs to have the following (potentially empty) fields
        #
        # {
        #   tool: ""
        #   errors: []
        #   warnings: []
        #   lint_errors: []
        #   lint_warning: []
        #   lint_infos: []
        # }
        #
        # where each entry is a string representing a lint message. This allows
        # to reuse the same LintCfg class with different tools since just the
        # parsing script that transforms the tool output into the hjson above
        # needs to be adapted.
        #
        # note that if this is a primary config, the results will
        # be generated using the _gen_results_summary function
        # '''

        # Generate results table for runs.
        results_str = "## " + self.results_title + "\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        if self.revision_string:
            results_str += "### " + self.revision_string + "\n"
        results_str += "### Lint Tool: " + self.tool.upper() + "\n\n"

        header = [
            "Build Mode", "Tool Warnings", "Tool Errors", "Lint Warnings",
            "Lint Errors"
        ]
        colalign = ("center", ) * len(header)
        table = [header]

        # aggregated counts
        self.result_summary["warnings"] = []
        self.result_summary["errors"] = []
        self.result_summary["lint_warnings"] = []
        self.result_summary["lint_errors"] = []

        fail_msgs = ""
        for mode in self.build_modes:

            result_data = Path(
                subst_wildcards(self.build_dir, {"build_mode": mode.name}) +
                '/results.hjson')
            log.info("looking for result data file at %s", result_data)

            try:
                with result_data.open() as results_file:
                    self.result = hjson.load(results_file, use_decimal=True)
            except IOError as err:
                log.warning("%s", err)
                self.result = {
                    "tool": "",
                    "errors": ["IOError: %s" % err],
                    "warnings": [],
                    "lint_errors": [],
                    "lint_warnings": [],
                    "lint_infos": []
                }
            if self.result:
                table.append([
                    mode.name,
                    str(len(self.result["warnings"])) + " W ",
                    str(len(self.result["errors"])) + " E",
                    # We currently do not publish these infos at
                    # the moment len(self.result["lint_infos"]),
                    str(len(self.result["lint_warnings"])) + " W",
                    str(len(self.result["lint_errors"])) + " E"
                ])
            else:
                self.result = {
                    "tool": "",
                    "errors": [],
                    "warnings": [],
                    "lint_errors": [],
                    "lint_warnings": [],
                    "lint_infos": []
                }

            self.result_summary["warnings"] += self.result["warnings"]
            self.result_summary["errors"] += self.result["errors"]
            self.result_summary["lint_warnings"] += self.result[
                "lint_warnings"]
            self.result_summary["lint_errors"] += self.result["lint_errors"]

            # Append detailed messages if they exist
            hdr_key_pairs = [("Tool Warnings", "warnings"),
                             ("Tool Errors", "errors"),
                             ("Lint Warnings", "lint_warnings"),
                             ("Lint Errors", "lint_errors")]


            # Lint fails if any warning or error message has occurred
            self.errors_seen = False
            for _, key in hdr_key_pairs:
                if key in self.result:
                    if self.result.get(key):
                        self.errors_seen = True
                        break

            if self.errors_seen:
                fail_msgs += "\n### Errors and Warnings for Build Mode `'" + mode.name + "'`\n"
                for hdr, key in hdr_key_pairs:
                    msgs = self.result.get(key)
                    fail_msgs += print_msg_list("#### " + hdr, msgs, self.max_msg_count)

        if len(table) > 1:
            self.results_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe",
                colalign=colalign) + "\n"

            # the email and published reports will default to self.results_md if they are
            # empty. in case they need to be sanitized, override them and do not append
            # detailed messages.
            if self.sanitize_email_results:
                self.email_results_md = self.results_md
            if self.sanitize_publish_results:
                self.publish_results_md = self.results_md
            # locally generated result always contains all details
            self.results_md += fail_msgs
        else:
            self.results_md = results_str + "\nNo results to display.\n"
            self.email_results_md = self.results_md
            self.publish_results_md = self.results_md

        # Write results to the scratch area
        self.results_file = self.scratch_path + "/results_" + self.timestamp + ".md"
        with open(self.results_file, 'w') as f:
            f.write(self.results_md)

        log.info("[results page]: [%s] [%s]", self.name, self.results_file)
        return self.results_md
