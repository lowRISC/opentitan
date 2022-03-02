#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Parses lint report and dump filtered messages in hjson format.
"""
import argparse
import re
import sys
from pathlib import Path

import hjson

# this allows both scientific and fixed point numbers
FP_NUMBER = r"[-+]?\d+\.\d+[Ee]?[-+]?\d*"
# fp relative error threshold for report checksums
CROSSCHECK_REL_TOL = 0.001


def _match_fp_number(full_file, patterns):
    """Extract numbers from patterns in full_file (a string)

    patterns is a list of pairs, (key, pattern). Each pattern should be a
    regular expression with exactly one capture group. Any match for group will
    be parsed as a float.

    Returns a pair (nums, errs) where nums is a dictionary keyed by the keys in
    patterns. The value at K is a list of floats matching patterns[K] if there
    was more than one match. If there was exactly one match for the
    patterns[K], the value at K is that float (rather than a singleton list).

    errs is a list of error messages (caused by failed float conversions or
    when there is no match for a pattern).

    """
    nums = {}
    errs = []
    for key, pattern in patterns:
        floats = []
        matches = re.findall(pattern, full_file, flags=re.MULTILINE)
        if not matches:
            errs.append('Pattern {!r} of key {!r} not found'.format(
                pattern, key))
            continue

        for match in matches:
            try:
                floats.append(float(match))
            except ValueError as err:
                errs.append('ValueError: {}'.format(err))

        if floats:
            nums[key] = floats[0] if len(floats) == 1 else floats

    return (nums, errs)


def _extract_messages(full_file, results, key, args):
    """
    This extracts error and warning messages from the sting buffer full_file.
    """
    err_warn_patterns = [("%s_errors" % key, r"^Error: .*"),
                         ("%s_errors" % key, r"^ERROR: .*"),
                         ("%s_errors" % key, r"^.*command not found.*"),
                         ("%s_warnings" % key, r"^Warning: .*"),
                         ("%s_warnings" % key, r"^WARNING: .*")]
    for severity, pattern in err_warn_patterns:
        results['messages'][severity] += re.findall(pattern,
                                                    full_file,
                                                    flags=re.MULTILINE)


def _extract_gate_eq(full_file, results, key, args):
    """
    This reads out the unit gate-equivalent.
    """
    try:
        results[key]["ge"] = float(full_file.strip())
    except ValueError as err:
        results["messages"]["flow_errors"] += ["ValueError: %s" % err]


def _rel_err(val, ref):
    """
    Calculate relative error with respect to reference
    """
    if ref == 0.0:
        return float("nan")
    else:
        return abs(val - ref) / ref


def _extract_area_recursive(full_file, results, key, args, depth=1, prefix=""):
    """
    This recursively extracts the area of submodules in the report.
    """
    # current depth level of sub-modules
    pattern = r"^(" + prefix + r"[\.0-9A-Za-z_\[\]]+){1}(?:(?:/[\.0-9A-Za-z_\[\]]+)*)"

    for k in range(5):
        pattern += r"\s+(" + FP_NUMBER + r")"
    matches = re.findall(pattern, full_file, flags=re.MULTILINE)

    # we drop the first entry as it always corresponds to the top-level
    # and for that we already parsed out the summary numbers.
    if matches and depth == 1:
        matches = matches[1:]

    instances = results[key]['instances']
    try:
        for match in matches:
            name = match[0]

            if name not in instances:
                instances.update({
                    name: {
                        "comb": 0.0,
                        "reg": 0.0,
                        "buf": float("nan"),  # not available here
                        "logic": 0.0,
                        "macro": 0.0,
                        "total": 0.0,
                        "depth": depth
                    }
                })

                # if we're not yet at depth, step one level down
                # if this module has been specified
                if name in args.expand_modules or depth < args.expand_depth:
                    _extract_area_recursive(full_file,
                                            results,
                                            key,
                                            args,
                                            depth=depth + 1,
                                            prefix=name + "/")

            comb = float(match[3])
            reg = float(match[4])
            macro = float(match[5])

            instance = instances[name]

            instance["comb"] += comb
            instance["reg"] += reg
            instance["logic"] += comb + reg
            instance["macro"] += macro
            instance["total"] += comb + reg + macro

    except ValueError as err:
        results["messages"]["flow_errors"] += ["ValueError: %s" % err]


def _check_area(results, key, args):
    """
    Checks whether the calculated area aggregates are
    consistent among depth levels.
    """

    instances = list(results[key]["instances"].values())
    names = list(results[key]["instances"].keys())
    for k, inst in enumerate(instances[:-1]):
        # checksums
        comb_check = 0.0
        reg_check = 0.0
        macro_check = 0.0
        do_check = False
        for subinst in instances[k + 1:]:
            # if the subinst is one level below, add the
            # numbers to the checksums.
            if inst['depth'] + 1 == subinst['depth']:
                comb_check += subinst["comb"]
                reg_check += subinst["reg"]
                macro_check += subinst["macro"]
                do_check = True

            # if the subinst is on the same level or above, stop the check
            elif inst['depth'] + 1 > subinst['depth']:
                break
        # if there where any submodules, perform the checks
        if do_check:
            checks = [("comb", comb_check), ("reg", reg_check),
                      ("macro", macro_check)]
            for name, val in checks:
                if _rel_err(val, inst[name]) > CROSSCHECK_REL_TOL:
                    results["messages"]["flow_errors"] += [
                        "Reporting error: %s check for %s: (%e) != (%e)" %
                        (name, names[k], val, inst[name])
                    ]


def _extract_area(full_file, results, key, args):
    """
    This extracts detailed area information from the report.
    Area will be reported in gate equivalents.
    """

    # this extracts the top-level summary
    patterns = [("comb", r"^Combinational area: \s* (\d+\.\d+)"),
                ("buf", r"^Buf/Inv area: \s* (\d+\.\d+)"),
                ("reg", r"^Noncombinational area: \s* (\d+\.\d+)"),
                ("macro", r"^Macro/Black Box area: \s* (\d+\.\d+)"),
                ("total", r"^Total cell area: \s* (\d+\.\d+)")]

    nums, errs = _match_fp_number(full_file, patterns)
    results['messages']['flow_errors'] += errs

    top_inst = {
        "comb": 0.0,
        "reg": 0.0,
        "buf": 0.0,
        "logic": 0.0,
        "macro": 0.0,
        "total": 0.0,
        "depth": 0
    }

    # only overwrite default values if a match has been returned
    for num in nums.keys():
        top_inst[num] = nums[num]

    top_inst['logic'] = top_inst['comb'] + top_inst['reg']
    results[key]["instances"].update({args.dut: top_inst})

    # this extracts submodules
    _extract_area_recursive(full_file, results, key, args)
    # second pass to crosscheck the calculated aggregates
    _check_area(results, key, args)


def _extract_clocks(full_file, results, key, args):
    """
    Parse out the clocks and their period
    """
    clocks = re.findall(r"^(.+)\s+(\d+\.?\d*)\s+\{\d+.?\d* \d+.?\d*\}\s+",
                        full_file,
                        flags=re.MULTILINE)
    try:
        # get clock period
        for k, c in enumerate(clocks):
            if c[0].strip() not in results[key]:
                results[key].update({
                    c[0].strip(): {
                        "tns": 0.0,
                        "wns": 0.0,
                        "period": float(c[1])
                    }
                })
    except ValueError as err:
        results["messages"]["flow_errors"] += ["ValueError: %s" % err]


def _extract_timing(full_file, results, key, args):
    """
    This extracts the TNS and WNS for all defined clocks.
    """
    groups = re.findall(r"^  Path Group:\s(.+)\s",
                        full_file,
                        flags=re.MULTILINE)

    slack = re.findall(r"^  slack \(.+\) \s*(" + FP_NUMBER + ")",
                       full_file,
                       flags=re.MULTILINE)
    try:
        # get TNS and WNS in that group
        for k, g in enumerate(groups):
            if g.strip() not in results[key]:
                results[key].update({
                    g.strip(): {
                        "tns": 0.0,
                        "wns": 0.0,
                        "period": float("nan")
                    }
                })
            value = float(slack[k]) if float(slack[k]) < 0.0 else 0.0
            results[key][g]["wns"] = min(results[key][g]["wns"], value)
            results[key][g]["tns"] += value
    except ValueError as err:
        results["messages"]["flow_errors"] += ["ValueError: %s" % err]


def _match_units(full_file, patterns, key, results):
    """
    Compares the match to the units given and stores the corresponding
    order of magnitude as a floating point value.
    """
    for subkey, pattern, units in patterns:
        match = re.findall(pattern, full_file, flags=re.MULTILINE)
        try:
            if match:
                if len(match[0]) == 2:
                    if match[0][1].strip() in units:
                        results[key][subkey] = float(match[0][0]) * \
                            units[match[0][1].strip()]
        except ValueError as err:
            results["messages"]["flow_errors"] += ["ValueError: %s" % err]


def _extract_units(full_file, results, key, args):
    """
    Get the SI units configuration of this run
    """
    patterns = [
        ("voltage", r"^    Voltage Units = (\d+\.?\d*)(nV|uV|mV|V)", {
            "nV": 1E-9,
            "uV": 1E-6,
            "mV": 1E-3,
            "V": 1E0
        }),
        ("capacitance", r"^    Capacitance Units = (\d+\.?\d*)(ff|pf|nf|uf)", {
            "ff": 1E-15,
            "pf": 1E-12,
            "nf": 1E-9,
            "uf": 1E-6
        }),
        ("time", r"^    Time Units = (\d+\.?\d*)(ps|ns|us|ms)", {
            "ps": 1E-12,
            "ns": 1E-9,
            "us": 1E-6,
            "ms": 1E-3
        }),
        ("dynamic", r"^    Dynamic Power Units = (\d+\.?\d*)(pW|nW|uW|mW|W)", {
            "pW": 1E-12,
            "nW": 1E-9,
            "uW": 1E-6,
            "mW": 1E-3,
            "W": 1E0
        }),
        ("static", r"^    Leakage Power Units = (\d+\.?\d*)(pW|nW|uW|mW|W)", {
            "pW": 1E-12,
            "nW": 1E-9,
            "uW": 1E-6,
            "mW": 1E-3,
            "W": 1E0
        })
    ]

    _match_units(full_file, patterns, key, results)


def _extract_power(full_file, results, key, args):
    """
    This extracts power estimates for the top module from the report.
    """

    # extract first 3 columns on that line
    patterns = [("net", r"^" + results["top"] + r"[a-zA-Z0-9_]*\s*(" + FP_NUMBER + r")\s*" +
                 FP_NUMBER + r"\s*" + FP_NUMBER),
                ("int", r"^" + results["top"] + r"[a-zA-Z0-9_]*\s*" + FP_NUMBER + r"\s*(" +
                 FP_NUMBER + r")\s*" + FP_NUMBER),
                ("leak", r"^" + results["top"] + r"[a-zA-Z0-9_]*\s*" + FP_NUMBER + r" \s*" +
                 FP_NUMBER + r"\s*(" + FP_NUMBER + r")")]

    nums, errs = _match_fp_number(full_file, patterns)

    # only overwrite default values if a match has been returned
    for num_key in nums.keys():
        results[key][num_key] = nums[num_key]

    results['messages']['flow_errors'] += errs


def _parse_file(path, name, results, handler, key, args):
    """
    Attempts to open and parse a given report file with the handler provided.
    """
    try:
        with Path(path).joinpath(name).open() as f:
            full_file = f.read()
            handler(full_file, results, key, args)
    except IOError as err:
        results["messages"]["flow_errors"] += ["IOError: %s" % err]


def get_results(args):
    """
    Parse report and corresponding logfiles and extract error, warning
    and info messages for each IP present in the result folder
    """

    results = {
        "tool": "dc",
        "top": "",
        "messages": {
            "flow_errors": [],
            "flow_warnings": [],
            "analyze_errors": [],
            "analyze_warnings": [],
            # Depending on the termination stage,
            # these message lists do not exist.
            "elab_errors": None,
            "elab_warnings": None,
            "compile_errors": None,
            "compile_warnings": None,
        },
    }

    results["top"] = args.dut

    args.expand_modules = args.expand_modules.strip().split(',')

    # Check whether the termination stage is known and define the
    # associated reports to be parsed.
    if args.termination_stage not in ["analyze", "elab", "compile", "reports"]:
        results['messages']['flow_errors'].append(
            'Unknown termination stage {}'.format(args.termination_stage))

    # We always run analysis, and we always look at the synthesis log.
    rep_types = [(args.log_path, 'synthesis.log', 'flow', _extract_messages),
                 (args.rep_path, 'analyze.rpt', 'analyze', _extract_messages)]

    if args.termination_stage in ["elab", "compile", "reports"]:
        rep_types += [(args.rep_path, 'elab.rpt', 'elab', _extract_messages)]
        results["messages"]["elab_errors"] = []
        results["messages"]["elab_warnings"] = []
    if args.termination_stage in ["compile", "reports"]:
        rep_types += [(args.rep_path, 'compile.rpt', 'compile', _extract_messages)]
        results["messages"]["compile_errors"] = []
        results["messages"]["compile_warnings"] = []
    if args.termination_stage in ["reports"]:
        rep_types += [(args.rep_path, 'gate_equiv.rpt', 'area', _extract_gate_eq),
                      (args.rep_path, 'area.rpt', 'area', _extract_area),
                      (args.rep_path, 'clocks.rpt', 'timing', _extract_clocks),
                      (args.rep_path, 'timing.rpt', 'timing', _extract_timing),
                      (args.rep_path, 'power.rpt', 'power', _extract_power),
                      (args.rep_path, 'power.rpt', 'units', _extract_units)]
        results.update({
            "timing": {
                # field for each timing group with tns, wns
                # and the period if this is a clock
            },
            "area": {
                # gate equivalent of a NAND2 gate
                "ge": float("nan"),
                # hierchical report with "comb", "buf", "reg", "macro", "total"
                "instances": {},
            },
            "power": {
                "net": float("nan"),
                "int": float("nan"),
                "leak": float("nan"),
            },
            "units": {
                "voltage": float("nan"),
                "capacitance": float("nan"),
                "time": float("nan"),
                "dynamic": float("nan"),
                "static": float("nan"),
            }
        })

    for path, name, key, handler in rep_types:
        _parse_file(path, name, results, handler, key, args)

    return results


def main():
    parser = argparse.ArgumentParser(
        description="""This script parses DC log and report files from
        a synthesis run, filters the messages and creates an aggregated result
        .hjson file with the following fields:

        results = {
            "tool": "dc",
            "top" : <name of toplevel>,

            "messages": {
                "flow_errors"      : [],
                "flow_warnings"    : [],
                "analyze_errors"   : [],
                "analyze_warnings" : [],
                "elab_errors"      : [],
                "elab_warnings"    : [],
                "compile_errors"   : [],
                "compile_warnings" : [],
            },

            "timing": {
                # per timing group (ususally a clock domain)
                # in nano seconds
                <group>  : {
                    "tns"    : <value>,
                    "wns"    : <value>,
                    "period" : <value>,
                ...
                }
            },

            "area": {
                # gate equivalent of a NAND2 gate
                "ge"     : <value>,

                # summary report, in GE
                "comb"   : <value>,
                "buf"    : <value>,
                "reg"    : <value>,
                "macro"  : <value>,
                "total"  : <value>,

                # hierchical report of first submodule level
                "instances" : {
                    <name> : {
                        "comb"  : <value>,
                        "buf"   : <value>,
                        "reg"   : <value>,
                        "macro" : <value>,
                        "total" : <value>,
                    },
                    ...
                },
            },

            "power": {
                "net"  : <value>,
                "int"  : <value>,
                "leak" : <value>,
            },

            "units": {
                "voltage"     : <value>,
                "capacitance" : <value>,
                "time"        : <value>,
                "dynamic"     : <value>,
                "static"      : <value>,
            }
        }

        The script returns nonzero status if any errors are present.
        """)

    parser.add_argument(
        '--dut',
        type=str,
        help="""Name of the DUT. This is needed to parse the reports.""")

    parser.add_argument('--log-path',
                        type=str,
                        help="""
                             Path to log files for the flow.
                             This script expects the following log files to be present:

                               - <log-path>/synthesis.log : output of synopsys shell

                             """)

    parser.add_argument('--rep-path',
                        type=str,
                        help="""
                             Path to report files of the flow.
                             This script expects the following report
                             files to be present:

                               - <rep-path>/analyze.rpt : output of analyze command
                               - <rep-path>/elab.rpt    : output of elab command
                               - <rep-path>/compile.rpt : output of compile_ultra
                               - <rep-path>/area.rpt    : output of report_area
                               - <rep-path>/timing.rpt  : output of report_timing
                               - <rep-path>/power.rpt   : output of report_power

                             """)

    parser.add_argument('--out-dir',
                        type=str,
                        default="./",
                        help="""Output directory for the 'results.hjson' file.
                        Defaults to './'""")

    parser.add_argument('--expand-depth',
                        type=int,
                        default=1,
                        help="""Area Report with hierarchical depth""")

    parser.add_argument(
        '--expand-modules',
        type=str,
        default="",
        help="""Comma separated list of modules to expand in area report""")

    parser.add_argument(
        '--termination-stage',
        type=str,
        default="",
        help="""Can be either 'analyze', 'elab', 'compile' or 'reports'""")

    args = parser.parse_args()
    results = get_results(args)

    with Path(
            args.out_dir).joinpath("results.hjson").open("w") as results_file:
        hjson.dump(results,
                   results_file,
                   ensure_ascii=False,
                   for_json=True,
                   use_decimal=True)

    # helper function
    def _getlen(x):
        return len(x) if x is not None else 0

    # return nonzero status if any warnings or errors are present
    # lint infos do not count as failures
    nr_errors = (_getlen(results["messages"]["flow_errors"]) +
                 _getlen(results["messages"]["analyze_errors"]) +
                 _getlen(results["messages"]["elab_errors"]) +
                 _getlen(results["messages"]["compile_errors"]))

    print("""------------- Summary -------------
Flow Warnings:      %s
Flow Errors:        %s
Analyze Warnings:   %s
Analyze Errors:     %s
Elab Warnings:      %s
Elab Errors:        %s
Compile Warnings:   %s
Compile Errors:     %s
-----------------------------------""" %
          (_getlen(results["messages"]["flow_warnings"]),
           _getlen(results["messages"]["flow_errors"]),
           _getlen(results["messages"]["analyze_warnings"]),
           _getlen(results["messages"]["analyze_errors"]),
           _getlen(results["messages"]["elab_warnings"]),
           _getlen(results["messages"]["elab_errors"]),
           _getlen(results["messages"]["compile_warnings"]),
           _getlen(results["messages"]["compile_errors"])))

    if nr_errors > 0:
        print("Synthesis not successful.")
        sys.exit(1)

    print("Synthesis successful.")
    sys.exit(0)


if __name__ == "__main__":
    main()
