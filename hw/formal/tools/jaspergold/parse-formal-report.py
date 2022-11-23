#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import logging as log
import re
from pathlib import Path
from collections import OrderedDict
import sys

import hjson


def extract_messages(str_buffer, patterns):
    '''Extract messages matching patterns from str_buffer as a dictionary.

    The patterns argument is a list of pairs, (key, pattern). Each pattern is a regex
    and all matches in str_buffer are stored in a dictionary under the paired key.
    '''
    results = OrderedDict()
    for key, pattern in patterns:
        val = results.setdefault(key, [])
        val += re.findall(pattern, str_buffer, flags=re.MULTILINE)

    return results


def extract_messages_count(str_buffer, patterns, exp_unproven_properties):
    '''Extract messages matching patterns from full_file as a dictionary.

    The patterns argument is a list of pairs, (key, pattern). Each pattern is a regex
    and the total count of all matches in str_buffer are stored in a dictionary under
    the paired key.
    If input argument `exp_unproven_properties` is not None, the total count will not
    include the expected properties. However, if the expected are not found in its
    category, will add the properties to the category.
    '''
    results = OrderedDict()
    for key, pattern in patterns:
        results.setdefault(key, 0)

        if exp_unproven_properties and key in exp_unproven_properties:
            matched_pattern = re.findall(pattern, str_buffer, flags=re.MULTILINE)
            for unproven_property in exp_unproven_properties[key]:
                unproven_property_found = 0
                for item in matched_pattern:
                    # If the expected unproven property is found, remove the item from the
                    # list of matched_pattern.
                    if unproven_property in item:
                        matched_pattern.remove(item)
                        unproven_property_found = 1
                # If expected unproven property is not found, add the property to the
                # list of matched pattern.
                if not unproven_property_found:
                    matched_pattern.append("Fail to find this property: " + unproven_property)
            results[key] += len(matched_pattern)
        else:
            results[key] += len(re.findall(pattern, str_buffer, flags=re.MULTILINE))

    return results


def format_percentage(good, bad):
    '''Return a percetange of good / (good + bad) with a format `100.00 %`.'''
    denom = good + bad
    pc = 100 * good / denom if denom else 0

    return '{0:.2f} %'.format(round(pc, 2))


def parse_message(str_buffer):
    '''Parse error, warnings, and failed properties from the log file'''
    err_warn_patterns = [("errors", r"^ERROR: .*"),
                         ("errors", r"^\[ERROR.*"),
                         ("warnings", r"^WARNING: .*"),
                         ("warnings", r"^\[WARN.*"),
                         ("cex", r"^\[\d+\]\s+(\S*)\s+cex.*"),
                         ("undetermined", r"^\[\d+\]\s+(\S*)\s+undetermined.*"),
                         ("unreachable", r"^\[\d+\]\s+(\S*)\s+unreachable.*")]
    return extract_messages(str_buffer, err_warn_patterns)


def get_expected_failures(exp_failure_path):
    '''Get expected fail properties from a hjson file otherwise return None.'''
    if exp_failure_path is None:
        return {}
    else:
        try:
            with open(exp_failure_path, 'r') as f:
                exp_failures = hjson.load(f, use_decimal=True, object_pairs_hook=OrderedDict)
                return exp_failures
        except ValueError:
            log.error("{} not found".format(exp_failure_path))
            return {}


def get_summary(str_buffer, exp_failures):
    '''Count errors, warnings, and property status from the log file'''
    message_patterns = [("errors", r"^ERROR: .*"),
                        ("errors", r"^\[ERROR.*"),
                        ("warnings", r"^WARNING: .*"),
                        ("warnings", r"^\[WARN.*"),
                        ("proven", r"^\[\d+\].*proven.*"),
                        ("cex", r"^\[\d+\].*cex.*"),
                        ("covered", r"^\[\d+\].*covered.*"),
                        ("undetermined", r"^\[\d+\].*undetermined.*"),
                        ("unreachable", r"^\[\d+\].*unreachable.*")]
    summary = extract_messages_count(str_buffer, message_patterns, exp_failures)

    # Undetermined properties are categorized as pass because we could not find
    # any counter-cases within the limited time of running.
    summary["pass_rate"] = format_percentage(summary["proven"] + summary["undetermined"],
                                             summary["cex"] + summary["unreachable"])
    summary["cov_rate"] = format_percentage(summary["covered"], summary["unreachable"])

    return summary


def get_results(logpath, exp_failure_path):
    '''Parse log file and extract info to a dictionary'''
    try:
        with Path(logpath).open() as f:
            results = OrderedDict()
            full_file = f.read()
            results["messages"] = parse_message(full_file)

            results["exp_failures"] = get_expected_failures(exp_failure_path)

            results["summary"] = get_summary(full_file, results["exp_failures"])
            return results

    except IOError as err:
        err_msg = 'IOError {}'.format(err)
        log.error("[get_results] IOError %s", err)
        return {'messages': {'errors': err_msg}}

    return results


def get_cov_results(logpath, dut_name):
    '''Parse coverage information from the log file'''
    try:
        with Path(logpath).open() as f:
            full_file = f.read()
            cov_pattern = r"\s*\|\d*.\d\d%\s\(\d*\/\d*\)"  # cov pattern: 100.00% (5/5)
            pattern_match = r"\s*\|(\d*.\d\d)%\s\(\d*\/\d*\)"  # extract percentage in cov_pattern
            coverage_patterns = \
                [("stimuli", r"^\|" + dut_name + pattern_match + cov_pattern + cov_pattern),
                 ("coi", r"^\|" + dut_name + cov_pattern + pattern_match + cov_pattern),
                 ("proof", r"^\|" + dut_name + cov_pattern + cov_pattern + pattern_match)]
            cov_results = extract_messages(full_file, coverage_patterns)
            for key, item in cov_results.items():
                if len(item) == 1:
                    cov_results[key] = item[0] + " %"
                else:
                    cov_results[key] = "N/A"
                    # Report ERROR but continue the parsing script.
                    log.info("ERROR: parse %s coverage error. Expect one matching value, get %s",
                             key, item)
            return cov_results

    except IOError as err:
        log.error("[get_cov_results] IOError %s", err)
        return None


def main():
    parser = argparse.ArgumentParser(
        description=
        '''This script parses the JasperGold formal log to extract below information.

        "messages": {
          "errors"      : []
          "warnings"    : []
          "cex"         : ["property1", "property2"...],
          "undetermined": [],
          "unreachable" : [],
        },
        "summary": {
          "errors"      : 0
          "warnings"    : 2
          "proven"      : 20,
          "cex"         : 5,
          "covered"     : 18,
          "undetermined": 7,
          "unreachable" : 2,
          "pass_rate"   : "90 %",
          "cover_rate"  : "90 %"
        },
        If coverage is enabled, this script will also parse the coverage result:
        "coverage": {
          stimuli: "90 %",
          coi    : "90 %",
          proof  : "80 %"
        }
        The script returns nonzero status if any errors or property failures including
        "cex, undetermined, unreachable" are presented.

        Note this script is capable of parsing jaspergold 2020.09 version.
        ''')
    parser.add_argument('--logpath',
                        type=str,
                        help=('The path of the formal log file that will be parsed.'))

    parser.add_argument('--reppath',
                        type=str,
                        default="results.hjson",
                        help=('Parsed output hjson file path. Defaults to '
                              '`results.hjson` under the current script directory.'))

    parser.add_argument('--cov',
                        type=int,
                        default=0,
                        help=('Enable parsing coverage data. '
                              'By default, coverage parsing is disabled.'))

    parser.add_argument('--dut',
                        type=str,
                        default=None,
                        help=('Tesbench name. '
                              'By default is empty, used for coverage parsing.'))

    parser.add_argument('--exp-fail-path',
                        type=str,
                        default=None,
                        help=('The path of a hjson file that contains expected failing properties.'
                              '''By default is empty, used only if there are properties that are
                               expected to fail.'''))

    args = parser.parse_args()

    results = get_results(args.logpath, args.exp_fail_path)

    if args.cov:
        results["coverage"] = get_cov_results(args.logpath, args.dut)

    with Path(args.reppath).open("w") as results_file:
        hjson.dump(results,
                   results_file,
                   ensure_ascii=False,
                   for_json=True,
                   use_decimal=True)

    # return nonzero status if any errors or property failures are present
    # TODO: currently allow warnings
    err_msgs = results["messages"]
    n_errors = len(err_msgs["errors"])
    n_failures = (len(err_msgs.get("cex")) + len(err_msgs.get("undetermined")) +
                  len(err_msgs.get("unreachable")))
    if n_errors > 0 or n_failures > 0:
        log.info("Found %d errors,  %d failures", n_errors, n_failures)

    log.info("Formal logfile parsed succesfully")
    return 0


if __name__ == "__main__":
    sys.exit(main())
