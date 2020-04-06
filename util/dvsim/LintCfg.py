# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing lint configuration object
"""

import logging as log
import sys
from pathlib import Path

from tabulate import tabulate

from Deploy import *
from Modes import *
from OneShotCfg import OneShotCfg
from utils import *


# helper function for printing messages
def _print_msg_list(msg_list_name, msg_list):
    md_results = ""
    if msg_list:
        md_results += "### %s\n" % msg_list_name
        md_results += "```\n"
        for msg in msg_list:
            msg_parts = msg.split()
            md_results += msg + "\n\n"
        md_results += "```\n"
    return md_results


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

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return LintCfg(flow_cfg_file, proj_root, args)

    def gen_results_summary(self):
        '''
        Gathers the aggregated results from all sub configs
        '''

        # Generate results table for runs.
        log.info("Create summary of lint results")

        results_str = "## " + self.results_title + " (Summary)\n\n"
        results_str += "### " + self.timestamp_long + "\n\n"

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
        # note that if this is a master config, the results will
        # be generated using the _gen_results_summary function
        # '''

        # Generate results table for runs.
        results_str = "## " + self.results_title + "\n\n"
        results_str += "### " + self.timestamp_long + "\n"
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
                with open(result_data, "r") as results_file:
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
            if sum([
                    len(self.result["warnings"]),
                    len(self.result["errors"]),
                    len(self.result["lint_warnings"]),
                    len(self.result["lint_errors"])
            ]):
                fail_msgs += "\n## Errors and Warnings for Build Mode `'" + mode.name + "'`\n"
                fail_msgs += _print_msg_list("Tool Errors",
                                             self.result["errors"])
                fail_msgs += _print_msg_list("Tool Warnings",
                                             self.result["warnings"])
                fail_msgs += _print_msg_list("Lint Errors",
                                             self.result["lint_errors"])
                fail_msgs += _print_msg_list("Lint Warnings",
                                             self.result["lint_warnings"])
                #fail_msgs += _print_msg_list("Lint Infos", results["lint_infos"])

        if len(table) > 1:
            self.results_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe",
                colalign=colalign) + "\n" + fail_msgs
        else:
            self.results_md = results_str + "\nNo results to display.\n"

        # Write results to the scratch area
        self.results_file = self.scratch_path + "/results_" + self.timestamp + ".md"
        with open(self.results_file, 'w') as f:
            f.write(self.results_md)

        log.info("[results page]: [%s] [%s]", self.name, results_file)
        return self.results_md
