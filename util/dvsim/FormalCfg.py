# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from pathlib import Path

import hjson
from tabulate import tabulate

from OneShotCfg import OneShotCfg
from utils import VERBOSE, subst_wildcards


class FormalCfg(OneShotCfg):
    """Derivative class for running formal tools.
    """

    flow = 'formal'

    def __init__(self, flow_cfg_file, hjson_data, args, mk_config):
        super().__init__(flow_cfg_file, hjson_data, args, mk_config)
        self.header = ["name", "errors", "warnings", "proven", "cex", "undetermined",
                       "covered", "unreachable", "pass_rate", "cov_rate"]

        # Default not to publish child cfg results.
        if "publish_report" in hjson_data:
            self.publish_report = hjson_data["publish_report"]
        else:
            self.publish_report = False
        self.sub_flow = hjson_data['sub_flow']
        self.summary_header = ["name", "pass_rate", "stimuli_cov", "coi_cov", "prove_cov"]
        self.results_title = self.name.upper() + " Formal " + self.sub_flow.upper() + " Results"

    def parse_dict_to_str(self, input_dict, excl_keys = []):
        # This is a helper function to parse dictionary items into a string.
        # This function has an optional input "excl_keys" for user to exclude
        # printing out certain items according to their keys.
        # Note this function did not sort the input dictionary's key value
        # before printing the keys and items. If input dictionary is not an
        # OrderedDictionary, print out key order is not predictable.
        # This function works for Hjson lib outputs because the lib uses an
        # OrderDict when it reads dictionaries.
        # Example Input:
        # {
        #   "unreachable": ["prop1, prop2, prop3"],
        #   "cex"        : ["prop1"],
        # }
        # Example Output:
        # string = "unreachable:
        # ```
        # prop1
        # prop2
        # prop3
        # ```
        # cex:
        # ```
        # prop1
        # ```"
        output_str = ""
        for key, item in input_dict.items():
            if (key not in excl_keys) and item:
                output_str += "\n" + key + ":\n"
                output_str += "```\n"
                output_str += "\n".join(item)
                output_str += "\n```\n"
        return output_str

    def get_summary(self, result):
        summary = []
        formal_summary = result.get("summary")
        if formal_summary is None:
            results_str = "No summary information found\n"
            summary.append("N/A")
        else:
            colalign = ("center", ) * len(self.header)
            table = [self.header]
            table.append([
                self.name,
                str(formal_summary["errors"]) + " E ",
                str(formal_summary["warnings"]) + " W ",
                str(formal_summary["proven"]) + " G ",
                str(formal_summary["cex"]) + " E ",
                str(formal_summary["undetermined"]) + " W ",
                str(formal_summary["covered"]) + " G ",
                str(formal_summary["unreachable"]) + " E ",
                formal_summary["pass_rate"],
                formal_summary["cov_rate"]
            ])
            summary.append(formal_summary["pass_rate"])
            if len(table) > 1:
                results_str = tabulate(table, headers="firstrow", tablefmt="pipe",
                                       colalign=colalign)
            else:
                results_str = "No content in summary\n"
                summary.append("N/A")
        return results_str, summary

    def get_coverage(self, result):
        summary = []
        formal_coverage = result.get("coverage")
        if formal_coverage is None:
            results_str = "No coverage information found\n"
            summary = ["N/A", "N/A", "N/A"]
        else:
            cov_header = ["stimuli", "coi", "proof"]
            cov_colalign = ("center", ) * len(cov_header)
            cov_table = [cov_header]
            cov_table.append([
                formal_coverage["stimuli"],
                formal_coverage["coi"],
                formal_coverage["proof"]
            ])
            summary.append(formal_coverage["stimuli"])
            summary.append(formal_coverage["coi"])
            summary.append(formal_coverage["proof"])

            if len(cov_table) > 1:
                results_str = tabulate(cov_table, headers="firstrow",
                                       tablefmt="pipe", colalign=cov_colalign)

            else:
                results_str = "No content in formal_coverage\n"
                summary = ["N/A", "N/A", "N/A"]
        return results_str, summary

    def gen_results_summary(self):
        # Gathers the aggregated results from all sub configs
        # The results_summary will only contain the passing rate and
        # percentages of the stimuli, coi, and proven coverage
        # The email_summary will contain all the information from results_md
        results_str = "## " + self.results_title + " (Summary)\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        if self.revision:
            results_str += "### " + self.revision + "\n"
        results_str += "### Branch: " + self.branch + "\n"
        results_str += "\n"

        colalign = ("center", ) * len(self.summary_header)
        table = [self.summary_header]
        for cfg in self.cfgs:
            try:
                table.append(cfg.result_summary[cfg.name])
            except KeyError as e:
                table.append([cfg.name, "ERROR", "N/A", "N/A", "N/A"])
                log.error("cfg: %s could not find generated results_summary: %s", cfg.name, e)
        if len(table) > 1:
            self.results_summary_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe", colalign=colalign)
        else:
            self.results_summary_md = results_str

        log.info("[result summary]: %s", self.results_summary_md)

        # Generate email results summary
        colalign = ("left", ) + ("center", ) * (len(self.header) - 1)
        email_table = [self.header]
        error_message = ""

        for cfg in self.cfgs:
            email_result = cfg.result.get("summary")
            if email_result is not None:
                email_table.append([
                    cfg.name,
                    str(email_result["errors"]) + " E ",
                    str(email_result["warnings"]) + " W ",
                    str(email_result["proven"]) + " G ",
                    str(email_result["cex"]) + " E ",
                    str(email_result["undetermined"]) + " W ",
                    str(email_result["covered"]) + " G ",
                    str(email_result["unreachable"]) + " E ",
                    email_result["pass_rate"],
                    email_result["cov_rate"]
                ])
            messages = cfg.result.get("messages")
            if messages is not None:
                # TODO: temp disable printing out warnings in results_summary
                # Will clean up formal warnings first, then display warnings
                error = self.parse_dict_to_str(messages, ["warnings"])
                if error:
                    error_message += "\n#### " + cfg.name + "\n"
                    error_message += error

        if len(email_table) > 1:
            self.email_summary_md = results_str + tabulate(
                email_table, headers="firstrow", tablefmt="pipe", colalign=colalign)
        self.email_summary_md += error_message

        return self.results_summary_md

    def _gen_results(self, results):
        # This function is called after the regression and looks for
        # results.hjson file with aggregated results from the formal logfile.
        # The hjson file is required to follow this format:
        # {
        #   "messages": {
        #      "errors"      : []
        #      "warnings"    : []
        #      "cex"         : ["property1", "property2"...],
        #      "undetermined": [],
        #      "unreachable" : [],
        #   },
        #
        #   "summary": {
        #      "errors"      : 0
        #      "warnings"    : 2
        #      "proven"      : 20,
        #      "cex"         : 5,
        #      "covered"     : 18,
        #      "undetermined": 7,
        #      "unreachable" : 2,
        #      "pass_rate"   : "90 %",
        #      "cover_rate"  : "90 %"
        #   },
        # }
        # The categories for property results are: proven, cex, undetermined,
        # covered, and unreachable.
        #
        # If coverage was enabled then results.hjson will also have an item that
        # shows formal coverage. It will have the following format:
        #   "coverage": {
        #      stimuli: "90 %",
        #      coi    : "90 %",
        #      proof  : "80 %"
        #   }
        results_str = "## " + self.results_title + "\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        if self.revision:
            results_str += "### " + self.revision + "\n"
        results_str += "### Branch: " + self.branch + "\n"
        results_str += "### Tool: " + self.tool.upper() + "\n"
        summary = [self.name]  # cfg summary for publish results

        assert len(self.deploy) == 1
        mode = self.deploy[0]

        if results[mode] == "P":
            result_data = Path(subst_wildcards(self.build_dir,
                                               {"build_mode": mode.name}),
                               'results.hjson')
            try:
                with open(result_data, "r") as results_file:
                    self.result = hjson.load(results_file, use_decimal=True)
            except IOError as err:
                log.warning("%s", err)
                self.result = {
                    "messages": {
                        "errors": ["IOError: %s" % err],
                    }
                }

        results_str += "\n\n## Formal " + self.sub_flow.upper() + " Results\n"
        formal_result_str, formal_summary = self.get_summary(self.result)
        results_str += formal_result_str
        summary += formal_summary

        if self.cov:
            results_str += "\n\n## Coverage Results\n"
            results_str += ("### Coverage html file dir: " +
                            self.scratch_path + "/default/formal-icarus\n\n")
            cov_result_str, cov_summary = self.get_coverage(self.result)
            results_str += cov_result_str
            summary += cov_summary
        else:
            summary += ["N/A", "N/A", "N/A"]

        if results[mode] != "P":
            results_str += "\n## List of Failures\n" + ''.join(
                mode.launcher.fail_msg.message)

        messages = self.result.get("messages")
        if messages is not None:
            results_str += self.parse_dict_to_str(messages)

        self.results_md = results_str

        # Generate result summary
        self.result_summary[self.name] = summary

        return self.results_md

    def _publish_results(self):
        ''' our agreement with tool vendors allows us to publish the summary
        results (as in gen_results_summary).

        In default this method does nothing: detailed messages from each child
        cfg will not be published.
        If the publish_report argument is set to true, this method will only
        publish a result summary of the child cfg.
        '''
        if self.publish_report:
            self.publish_results_md = self.gen_results_summary()
            super()._publish_results()
        else:
            return
