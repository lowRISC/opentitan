# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing synthesis configuration object
"""

import logging as log
from pathlib import Path

import hjson
from tabulate import tabulate

from OneShotCfg import OneShotCfg
from utils import subst_wildcards


class SynCfg(OneShotCfg):
    """Derivative class for synthesis purposes.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        super().__init__(flow_cfg_file, proj_root, args)

    def __post_init__(self):
        super().__post_init__()
        # Set the title for synthesis results.
        self.results_title = self.name.upper() + " Synthesis Results"

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return SynCfg(flow_cfg_file, proj_root, args)

    def gen_results_summary(self):
        '''
        Gathers the aggregated results from all sub configs
        '''

        # Generate results table for runs.
        log.info("Create summary of synthesis results")

        results_str = "## " + self.results_title + " (Summary)\n\n"
        results_str += "### " + self.timestamp_long + "\n\n"

        self.results_summary_md = results_str + "\nNot supported yet.\n"

        print(self.results_summary_md)

        # Return only the tables
        return self.results_summary_md

    def _gen_results(self):
        # '''
        # The function is called after the regression has completed. It looks
        # for a regr_results.hjson file with aggregated results from the
        # synthesis run. The hjson needs to have the following (potentially
        # empty) fields
        #
        # results = {
        #     "tool": "dc",
        #     "top" : <name of toplevel>,
        #
        #     "messages": {
        #         "flow_errors"      : [],
        #         "flow_warnings"    : [],
        #         "analyze_errors"   : [],
        #         "analyze_warnings" : [],
        #         "elab_errors"      : [],
        #         "elab_warnings"    : [],
        #         "compile_errors"   : [],
        #         "compile_warnings" : [],
        #     },
        #
        #     "timing": {
        #         # per timing group (ususally a clock domain)
        #         # in nano seconds
        #         <group>  : {
        #             "tns"    : <value>,
        #             "wns"    : <value>,
        #             "period" : <value>,
        #         ...
        #         }
        #     },
        #
        #     "area": {
        #         # gate equivalent of a NAND2 gate
        #         "ge"     : <value>,
        #
        #         # summary report, in GE
        #         "comb"   : <value>,
        #         "buf"    : <value>,
        #         "reg"    : <value>,
        #         "macro"  : <value>,
        #         "total"  : <value>,
        #
        #         # hierchical report of first submodule level
        #         "instances" : {
        #             <name> : {
        #               "comb"  : <value>,
        #               "buf"   : <value>,
        #               "reg"   : <value>,
        #               "macro" : <value>,
        #               "total" : <value>,
        #             },
        #             ...
        #         },
        #     },
        #
        #     "power": {
        #         "net"  : <value>,
        #         "int"  : <value>,
        #         "leak" : <value>,
        #     },
        #
        #     "units": {
        #         "voltage"     : <value>,
        #         "capacitance" : <value>,
        #         "time"        : <value>,
        #         "dynamic"     : <value>,
        #         "static"      : <value>,
        #     }
        # }
        #
        # note that if this is a master config, the results will
        # be generated using the _gen_results_summary function
        # '''

        def _create_entry(val, norm=1.0, total=None, perctag="%"):
            """
            Create normalized entry with an optional
            percentage appended in brackets.
            """
            if val is not None and norm is not None:
                if total is not None:
                    perc = float(val) / float(total) * 100.0
                    entry = "%2.1f %s" % (perc, perctag)
                else:
                    value = float(val) / norm
                    entry = "%2.1f" % (value)
            else:
                entry = "--"

            return entry

        self.result = {}

        # Generate results table for runs.
        results_str = "## " + self.results_title + "\n\n"
        results_str += "### " + self.timestamp_long + "\n"
        results_str += "### Synthesis Tool: " + self.tool.upper() + "\n\n"

        # TODO: extend this to support multiple build modes
        for mode in self.build_modes:

            # results_str += "## Build Mode: " + mode.name + "\n\n"

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
                    "messages": {
                        "flow_errors": ["IOError: %s" % err],
                        "flow_warnings": [],
                        "analyze_errors": [],
                        "analyze_warnings": [],
                        "elab_errors": [],
                        "elab_warnings": [],
                        "compile_errors": [],
                        "compile_warnings": [],
                    },
                }

            # Message summary
            # results_str += "### Tool Message Summary\n\n"
            if "messages" in self.result:

                header = [
                    "Build Mode", "Flow Warnings", "Flow Errors",
                    "Analyze Warnings", "Analyze Errors", "Elab Warnings",
                    "Elab Errors", "Compile Warnings", "Compile Errors"
                ]
                colalign = ("left", ) + ("center", ) * (len(header) - 1)
                table = [header]

                messages = self.result["messages"]
                table.append([
                    mode.name,
                    str(len(messages["flow_warnings"])) + " W ",
                    str(len(messages["flow_errors"])) + " E ",
                    str(len(messages["analyze_warnings"])) + " W ",
                    str(len(messages["analyze_errors"])) + " E ",
                    str(len(messages["elab_warnings"])) + " W ",
                    str(len(messages["elab_errors"])) + " E ",
                    str(len(messages["compile_warnings"])) + " W ",
                    str(len(messages["compile_errors"])) + " E ",
                ])

                if len(table) > 1:
                    results_str += tabulate(table,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign) + "\n\n"
                else:
                    results_str += "No messages found\n\n"
            else:
                results_str += "No messages found\n\n"

            # Hierarchical Area report
            results_str += "### Circuit Complexity in [kGE]\n\n"
            if "area" in self.result:

                header = [
                    "Instance", "Comb ", "Buf/Inv", "Regs", "Macros", "Total",
                    "Total [%]"
                ]
                colalign = ("left", ) + ("center", ) * (len(header) - 1)
                table = [header]

                # print top-level summary first
                row = ["**" + self.result["top"] + "**"]
                try:
                    kge = float(self.result["area"]["ge"]) * 1000.0

                    for field in ["comb", "buf", "reg", "macro", "total"]:
                        row += [
                            "**" +
                            _create_entry(self.result["area"][field], kge) +
                            "**"
                        ]

                    row += ["**--**"]
                    table.append(row)

                    # go through submodules
                    for name in self.result["area"]["instances"].keys():
                        if name == self.result["top"]:
                            continue
                        row = [name]
                        for field in ["comb", "buf", "reg", "macro", "total"]:
                            row += [
                                _create_entry(
                                    self.result["area"]["instances"][name]
                                    [field], kge)
                            ]

                        # add percentage  of total
                        row += [
                            _create_entry(
                                self.result["area"]["instances"][name][field],
                                kge, self.result["area"]["total"], "%u")
                        ]

                        table.append(row)

                except TypeError:
                    results_str += "Gate equivalent is not properly defined\n\n"

                if len(table) > 1:
                    results_str += tabulate(table,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign) + "\n\n"
                else:
                    results_str += "No area report found\n\n"
            else:
                results_str += "No area report found\n\n"

            # Timing report
            results_str += "### Timing in [ns]\n\n"
            if "timing" in self.result and "units" in self.result:

                header = ["Clock", "Period", "WNS", "TNS"]
                colalign = ("left", ) + ("center", ) * (len(header) - 1)
                table = [header]

                for clock in self.result["timing"].keys():
                    row = [clock]
                    row += [
                        _create_entry(
                            self.result["timing"][clock]["period"],
                            1.0E-09 / float(self.result["units"]["time"])),
                        _create_entry(
                            self.result["timing"][clock]["wns"], 1.0E-09 /
                            float(self.result["units"]["time"])) + " EN",
                        _create_entry(
                            self.result["timing"][clock]["tns"], 1.0E-09 /
                            float(self.result["units"]["time"])) + " EN"
                    ]
                    table.append(row)

                if len(table) > 1:
                    results_str += tabulate(table,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign) + "\n\n"
                else:
                    results_str += "No timing report found\n\n"
            else:
                results_str += "No timing report found\n\n"

            # Power report
            results_str += "### Power Estimates in [mW]\n\n"
            if "power" in self.result and "units" in self.result:

                header = ["Network", "Internal", "Leakage", "Total"]
                colalign = ("center", ) * len(header)
                table = [header]

                try:
                    self.result["power"]["net"]

                    power = [
                        float(self.result["power"]["net"]) *
                        float(self.result["units"]["dynamic"]),
                        float(self.result["power"]["int"]) *
                        float(self.result["units"]["dynamic"]),
                        float(self.result["power"]["leak"]) *
                        float(self.result["units"]["static"])
                    ]

                    total_power = sum(power)

                    row = [_create_entry(power[0], 1.0E-3) + " / " +
                           _create_entry(power[0], 1.0E-3, total_power),
                           _create_entry(power[1], 1.0E-3) + " / " +
                           _create_entry(power[1], 1.0E-3, total_power),
                           _create_entry(power[2], 1.0E-3) + " / " +
                           _create_entry(power[2], 1.0E-3, total_power),
                           _create_entry(total_power, 1.0E-3)]

                    table.append(row)
                # in case fp values are NoneType
                except TypeError:
                    results_str += "No power report found\n\n"

                if len(table) > 1:
                    results_str += tabulate(table,
                                            headers="firstrow",
                                            tablefmt="pipe",
                                            colalign=colalign) + "\n\n"
            else:
                results_str += "No power report found\n\n"

            # TODO: add support for pie / bar charts for area splits and
            # QoR history

        self.results_md = results_str
        # Write results to the scratch area
        self.results_file = self.scratch_path + "/results_" + self.timestamp + ".md"
        log.info("Detailed results are available at %s", self.results_file)
        with open(self.results_file, 'w') as f:
            f.write(self.results_md)

        return self.results_md
