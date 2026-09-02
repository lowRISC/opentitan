#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
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


def drop_expected_messages(key, matched, exp_unproven_properties):
    '''Drop one matched message per expected property, and flag the ones that are absent.

    Matching is by substring, so an expected property drops exactly one message rather than every
    message it appears in: one entry in the expected-failure file waives one property. An entry
    matching nothing is reported and left in the count, because a waiver naming a property the run
    did not produce is either stale or misspelled and must not pass unnoticed.
    '''
    remaining = list(matched)
    for unproven_property in exp_unproven_properties:
        found = next((item for item in remaining if unproven_property in item), None)
        if found is None:
            log.error(
                "Expected %s property '%s' is not in the report, so it is counted as a failure. "
                "The expected-failure file is stale or the name is wrong.", key,
                unproven_property)
            remaining.append("Fail to find this property: " + unproven_property)
        else:
            remaining.remove(found)

    return remaining


def extract_messages_count(str_buffer, patterns, exp_unproven_properties):
    '''Extract messages matching patterns from str_buffer as a dictionary.

    The patterns argument is a list of pairs, (key, pattern). Each pattern is a regex
    and the total count of all matches in str_buffer are stored in a dictionary under
    the paired key.
    If `exp_unproven_properties` is given, each property expected to fail under a key drops one
    match from that key's count, and a property that is not there is counted as a failure instead.
    See drop_expected_messages.
    Several patterns may share one key, so the matches are gathered per key before the expected
    properties are dropped. Dropping them per pattern would instead apply a waiver once for every
    pattern under the key, and a waiver removing a message under one pattern while being reported
    absent under the next leaves the count unchanged.
    '''
    matched = OrderedDict()
    for key, pattern in patterns:
        matched.setdefault(key, [])
        matched[key] += re.findall(pattern, str_buffer, flags=re.MULTILINE)

    results = OrderedDict()
    for key, messages in matched.items():
        if exp_unproven_properties and key in exp_unproven_properties:
            messages = drop_expected_messages(key, messages, exp_unproven_properties[key])
        results[key] = len(messages)

    return results


def get_expected_failures(exp_failure_path):
    '''Return the expected failing properties from a hjson file, or an empty dict if there are none.

    An unreadable or malformed file yields an empty dict, so no property is waived and nothing the
    run failed is hidden. It must not raise instead: the exception would escape into the caller's
    own `except IOError`, which would report the log file as the one that could not be opened and
    then leave main() to fail on a results dictionary that was never filled in.
    '''
    if not exp_failure_path:
        return {}

    try:
        with Path(exp_failure_path).open() as f:
            return hjson.load(f, use_decimal=True, object_pairs_hook=OrderedDict)
    except OSError as err:
        log.error("Cannot read the expected-failure file %s: %s. No property is waived.",
                  exp_failure_path, err)
        return {}
    except ValueError as err:
        log.error("Cannot parse the expected-failure file %s: %s. No property is waived.",
                  exp_failure_path, err)
        return {}


def format_percentage(good, bad):
    '''Return a percentage of good / (good + bad) with a format `100.00 %`.'''
    denom = good + bad
    pc = 100 * good / denom if denom else 0

    return '{0:.2f} %'.format(round(pc, 2))


def parse_message(str_buffer):
    '''Parse error, warnings, and failed properties from the log file'''
    err_warn_patterns = [("errors", r"^Error.*"),
                         ("errors", r"^\[Error.*"),
                         ("warnings", r"^Warning.*"),
                         ("warnings", r"^\[Warning.*"),
                         ("cex", r"^\d+,assert,falsified,.*"),
                         ("cex", r"^\d+,assert,vacuous,.*"),
                         ("undetermined", r"^\d+,assert,inconclusive,.*"),
                         ("unreachable", r"^\d+,cover,uncoverable,.*"),
                         ("undetermined", r"^\d+,cover,inconclusive,.*")]
    return extract_messages(str_buffer, err_warn_patterns)


def get_summary(str_buffer, exp_failures):
    '''Count errors, warnings, and property status from the log file'''
    message_patterns = [("errors", r"^Error.*"),
                        ("errors", r"^\[Error.*"),
                        ("warnings", r"^Warning.*"),
                        ("warnings", r"^\[Warning.*"),
                        ("proven", r"^\d+,assert,proven,.*"),
                        ("cex", r"^\d+,assert,falsified,.*"),
                        ("cex", r"^\d+,assert,vacuous,.*"),
                        ("undetermined", r"^\d+,assert,inconclusive,.*"),
                        ("covered", r"^\d+,cover,covered,.*"),
                        ("unreachable", r"^\d+,cover,uncoverable,.*"),
                        ("undetermined", r"^\d+,cover,inconclusive,.*")]
    summary = extract_messages_count(str_buffer, message_patterns, exp_failures)

    summary["pass_rate"] = format_percentage(summary["proven"],
                                             summary["cex"] + summary["undetermined"])
    summary["cov_rate"] = format_percentage(summary["covered"],
                                            summary["unreachable"])

    return summary


def get_results(logpath, exp_failure_path):
    '''Parse log file and extract info to a dictionary'''
    try:
        with Path(logpath).open() as f:
            results = OrderedDict()
            full_file = f.read()
            results["messages"] = parse_message(full_file)
            results["exp_failures"] = get_expected_failures(exp_failure_path)
            summary = get_summary(full_file, results["exp_failures"])
            if summary:
                results["summary"] = summary
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
                    log.warning("Parse %s coverage error. Expect one matching value, get %s",
                                key, item)
            return cov_results

    except IOError as err:
        log.error("[get_cov_results] IOError %s", err)
        return None


def main():
    parser = argparse.ArgumentParser(
        description=
        '''This script parses the output log to extract below information.

        "messages": {
          "errors"      : []
          "warnings"    : []
          "cex"         : ["property1", "property2"...],
          "vacuous"     : ["property5", "property6"...],
          "undetermined": [],
          "unreachable" : [],
        },
        "summary": {
          "errors"      : 0
          "warnings"    : 2
          "proven"      : 40,
          "cex"         : 5,
          "vacuous"     : 3,
          "covered"     : 18,
          "undetermined": 2,
          "unreachable" : 2,
          "pass_rate"   : "80 %",
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

        Note this script is compatible with VC Formal version 2020.12-SP2.
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
                               expected to fail. If input is an empty string, will treat it as not
                               passing a file.'''))

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
