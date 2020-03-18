# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import csv
import os
import logging as log
from pathlib import Path

from tabulate import tabulate

from OneShotCfg import OneShotCfg
from utils import subst_wildcards


class FpvCfg(OneShotCfg):
    """Derivative class for fpv purposes.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        super().__init__(flow_cfg_file, proj_root, args)
        self.header = ["name", "proven", "cex", "undetermined", "covered", "unreachable",
                       "pass_rate", "cov_rate"]
        self.summary_header = ["name", "pass_rate", "stimuli_cov", "coi_cov", "prove_cov"]

    def __post_init__(self):
        super().__post_init__()
        self.results_title = self.name.upper() + " FPV Results"

    def gen_results_summary(self):
        # '''
        # Gathers the aggregated results from all sub configs
        # The result summary will only contains a percentage to the passing
        # rate, Stimuli coverage, COI coverage, and Proven coverage
        # '''
        log.info("Create summary of FPV results")

        results_str = "## " + self.results_title + " (Summary)\n\n"
        results_str += "### " + self.timestamp_long + "\n\n"

        colalign = ("center", ) * len(self.summary_header)
        table = [self.summary_header]
        for cfg in self.cfgs:
            for key in cfg.result_summary:
                try:
                    table.append(cfg.result_summary[key])
                except Exception as e:
                    table.append([key, "ERROR", "N/A", "N/A", "N/A"])
                    log.error("cfg:%s item: %s could not find generated result: %s", cfg, key, e)
        if len(table) > 1:
            self.results_summary_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe", colalign=colalign)
        else:
            self.results_summary_md = results_str

        print(self.results_summary_md)

        # Generate email results summary
        colalign = ("left", ) + ("center", ) * (len(self.header) - 1)
        email_table = [self.header]

        for cfg in self.cfgs:
            email_table.append([
                cfg.name,
                str(cfg.result["proven"]) + " G ",
                str(cfg.result["cex"]) + " E ",
                str(cfg.result["undetermined"]) + " W ",
                str(cfg.result["covered"]) + " G ",
                str(cfg.result["unreachable"]) + " W ",
                cfg.result["pass_rate"],
                cfg.result["cov_rate"]])
        if len(email_table) > 1:
            self.email_summary_md = results_str + tabulate(
                email_table, headers="firstrow", tablefmt="pipe", colalign=colalign)

        return self.results_summary_md

    def _gen_results(self):
        # '''
        # This function is called after the regression and looks for results.csv
        # file in the following format:
        #   property1,proven
        #   property2,cex
        #   property3,undetermined
        #   property4,unreachable
        #   ...
        # The categories for property results are: proven, cex, undetermined,
        # covered, and unreachable
        #
        # This function also looks for coverage result cov.csv if cov is enabled.
        # Cov.csv is formatted as below:
        #   Stimuli,90%
        #   COI,90%
        #   Proof,80%
        # '''
        results_str = "## " + self.results_title + "\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        results_str += "### FPV Tool: " + self.tool.upper() + "\n"
        results_str += "### LogFile dir: " + self.scratch_path + "/default \n\n"

        colalign = ("center", ) * len(self.header)
        table = [self.header]
        self.result = {
            "proven": 0,
            "cex": 0,
            "undetermined": 0,
            "covered": 0,
            "unreachable": 0,
            "pass_rate": 0,
            "cov_rate": 0
        }
        cov_header = ["stimuli", "coi", "proof"]
        cov_table = [cov_header]
        cov_colalign = ("center", ) * len(cov_header)

        for mode in self.build_modes:
            result_data = Path(subst_wildcards(self.build_dir, {"build_mode": mode.name}) +
                               '/results.csv')
            try:
                with open(result_data, "r") as results_file:
                    reader = csv.reader(results_file)
                    result = dict((rows[0], rows[1]) for rows in reader)
                    for key in result:
                        self.result[result[key]] = self.result.get(result[key]) + 1
                    total_tests = (self.result.get("proven") + self.result.get("cex") +
                                   self.result.get("undetermined"))
                    if total_tests == 0:
                        self.result["pass_rate"] = "{0:.2f} %".format(0.00)
                    else:
                        pass_rate = ((self.result.get("proven") +
                                      self.result.get("undetermined")) / total_tests * 100)
                        self.result["pass_rate"] = "{0:.2f} %".format(round(pass_rate, 2))
                    total_covs = self.result.get("covered") + self.result.get("unreachable")
                    if total_covs == 0:
                        self.result["cov_rate"] = "{0:.2f} %".format(0.00)
                    else:
                        cov_rate = self.result.get("covered") / total_covs * 100
                        self.result["cov_rate"] = "{0:.2f} %".format(round(cov_rate, 2))

                    table.append([
                        self.name,
                        self.result["proven"],
                        self.result["cex"],
                        self.result["undetermined"],
                        self.result["covered"],
                        self.result["unreachable"],
                        self.result["pass_rate"],
                        self.result["cov_rate"]])
                os.remove(result_data)
            except IOError as err:
                log.warning("%s", err)
                results_str += "No FPV result file: " + str(result_data)

            if (self.cov):
                cov_data = Path(
                    subst_wildcards(self.build_dir, {"build_mode": mode.name}) + "/cov.csv")
                try:
                    with open(cov_data, "r") as results_file:
                        reader = csv.reader(results_file)
                        cov_result = dict((rows[0], rows[1]) for rows in reader)
                        cov_percentage = []
                        for cov_name in cov_header:
                            if cov_name in cov_result:
                                format_perc = cov_result[cov_name].replace("%", " %")
                                cov_percentage.append(format_perc)
                        cov_table.append(cov_percentage)
                    os.remove(cov_data)
                except IOError as err:
                    log.warning("%s", err)
                    results_str += str(err)

        if table != [self.header]:
            self.results_md = results_str + tabulate(
                table, headers="firstrow", tablefmt="pipe", colalign=colalign)
        else:
            self.results_md = results_str

        # Generate coverage result
        if (self.cov):
            results_str = "\n\n## Coverage Results\n"
            results_str += ("### Coverage html file dir: " +
                            self.scratch_path + "/default/formal-icarus \n\n")
            if cov_table != [cov_header]:
                self.results_md += (results_str + tabulate(cov_table,
                                                           headers="firstrow",
                                                           tablefmt="pipe",
                                                           colalign=cov_colalign))
            else:
                self.results_md += results_str

        # Write results to the scratch area
        self.results_file = self.scratch_path + "/results_" + self.timestamp + ".md"
        with open(self.results_file, 'w') as f:
            f.write(self.results_md)

        log.info("[results page]: [%s] [%s]", self.name, self.results_file)

        # Generate result summary
        summary = [self.name, self.result["pass_rate"]]
        if (self.cov and cov_table != [cov_header]):
            for item in cov_table[1]:
                summary.append(item)
        else:
            summary += ["N/A", "N/A", "N/A"]
        self.result_summary[self.name] = summary

        return self.results_md

    def _publish_results(self):
        '''Upon agreement with tool vendors, this script will only publish the result summary to
        the public domain.
        Individual detailed results/numbers will not be uploaded.
        '''
        return
