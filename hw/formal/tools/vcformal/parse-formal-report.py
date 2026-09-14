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


# The engine this parser reports on. common_formal_cfg.hjson invokes
# `{formal_root}/tools/{tool}/parse-formal-report.py`, so the directory holding this script is the
# tool name by the flow's own contract, and an expected-failure file uses that name to scope a
# waiver to one engine.
TOOL = Path(__file__).resolve().parent.name

# The engines that have a parser, which are the sibling directories holding one. A section named
# anything else is a typo, and a typo in a section name is the one mistake in an expected-failure
# file that nothing downstream would otherwise catch: the section simply never matches, so the
# file waives nothing and says nothing.
KNOWN_TOOLS = frozenset(
    entry.name for entry in Path(__file__).resolve().parent.parent.iterdir()
    if (entry / Path(__file__).name).is_file())

# Every log.error below is the flow's failure signal, not just a note. Logging's default format
# prefixes the line with `ERROR:`, and common_formal_cfg.hjson sets
# `build_fail_patterns: ["^ERROR:.*$"]`, so dvsim fails the job on any one of them. That is what
# lets this script report a bad expected-failure file and still exit 0. Keep new diagnostics at
# error level unless they are genuinely advisory, and do not reformat them without checking that
# pattern still matches.


SUMMARY_PATTERNS = [("errors", r"^Error.*"),
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

# The categories a waiver may name, which are exactly the ones counted above.
WAIVER_CATEGORIES = frozenset(key for key, _ in SUMMARY_PATTERNS)


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
    '''Drop one matched message per expected property, and flag the ones that do not apply.

    Matching is by substring, so an expected property drops exactly one message rather than every
    message it appears in: one entry in the expected-failure file waives one property. An entry
    that matches nothing, and an entry that matches several messages, both waive nothing and are
    reported. A waiver naming a property the run did not produce is stale or misspelled, and one
    matching several properties is too short to say which of them it meant, so neither may pass
    unnoticed.

    The stand-ins for entries that matched nothing are held apart from the real messages until the
    end, so that a later entry cannot match the text of an earlier entry's stand-in.
    '''
    remaining = list(matched)
    unmatched = []
    for unproven_property in exp_unproven_properties:
        found = [item for item in remaining if unproven_property in item]
        if not found:
            log.error(
                "Expected %s property '%s' is not in the report, so it is counted as a failure. "
                "The expected-failure file is stale or the name is wrong.", key,
                unproven_property)
            unmatched.append("Fail to find this property: " + unproven_property)
        elif len(found) > 1:
            log.error(
                "Expected %s property '%s' matches %d messages, so it is ambiguous and waives "
                "none of them. Give the property name in full.", key, unproven_property,
                len(found))
        else:
            remaining.remove(found[0])

    return remaining + unmatched


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


def check_waiver_categories(waivers, exp_failure_path):
    '''Return the waivers unchanged, or an empty dict if any category is unusable.

    A category outside WAIVER_CATEGORIES is one get_summary never counts under, so it would waive
    nothing however it is spelled. A category holding a bare string rather than a list would be
    iterated one character at a time by drop_expected_messages, and most single characters match
    some message, so the count would come out wrong. Neither is caught anywhere downstream.
    '''
    for category, properties in waivers.items():
        if category not in WAIVER_CATEGORIES:
            log.error(
                "%s names category '%s', which is not one this parser counts. Expected one of "
                "%s. No property is waived.", exp_failure_path, category,
                ", ".join(sorted(WAIVER_CATEGORIES)))
            return {}

        if not isinstance(properties, list) or not all(isinstance(p, str) for p in properties):
            log.error(
                "%s category '%s' must hold a list of property names. No property is waived.",
                exp_failure_path, category)
            return {}

    return waivers


def select_tool_waivers(exp_failures, tool, exp_failure_path):
    '''Return the waivers in an expected-failure file that apply to one tool.

    Two shapes are accepted. A file whose top-level values are lists is the flat form, which
    applies to every engine and is what every file in the tree was before sections existed. A file
    whose top-level values are mappings is keyed by tool name, and only the section naming this
    engine applies.

    Sections are what make a waiver correct across engines, because a property name is only
    meaningful to the engine that emits it. The `:precondition1` cover items every file in the tree
    waives are synthesised by JasperGold and have no VC Formal equivalent, so a flat file waiving
    them has VC Formal count all three as failures for being absent.
    '''
    if not exp_failures:
        return {}

    values = list(exp_failures.values())
    if all(isinstance(value, list) for value in values):
        return check_waiver_categories(exp_failures, exp_failure_path)

    if all(isinstance(value, dict) for value in values):
        unknown = sorted(set(exp_failures) - KNOWN_TOOLS)
        if unknown:
            log.error(
                "%s has section(s) %s, which name no engine with a parser. Expected one of %s. "
                "No property is waived.", exp_failure_path, ", ".join(unknown),
                ", ".join(sorted(KNOWN_TOOLS)))
            return {}

        waivers = exp_failures.get(tool)
        if waivers is None:
            log.info("%s has no %s section, so no property is waived for this engine.",
                     exp_failure_path, tool)
            return {}
        return check_waiver_categories(waivers, exp_failure_path)

    log.error("%s mixes per-tool sections with bare categories, so it cannot be read. "
              "No property is waived.", exp_failure_path)
    return {}


def get_expected_failures(exp_failure_path, tool):
    '''Return the expected failing properties that apply to one tool, or an empty dict if none.

    An unreadable or malformed file yields an empty dict, so no property is waived and nothing the
    run failed is hidden. It must not raise instead: the exception would escape into the caller's
    own `except IOError`, which would report the log file as the one that could not be opened and
    then leave main() to fail on a results dictionary that was never filled in.
    '''
    if not exp_failure_path:
        return {}

    try:
        with Path(exp_failure_path).open() as f:
            exp_failures = hjson.load(f, use_decimal=True, object_pairs_hook=OrderedDict)
    except OSError as err:
        log.error("Cannot read the expected-failure file %s: %s. No property is waived.",
                  exp_failure_path, err)
        return {}
    except ValueError as err:
        log.error("Cannot parse the expected-failure file %s: %s. No property is waived.",
                  exp_failure_path, err)
        return {}

    return select_tool_waivers(exp_failures, tool, exp_failure_path)


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
    summary = extract_messages_count(str_buffer, SUMMARY_PATTERNS, exp_failures)

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
            results["exp_failures"] = get_expected_failures(exp_failure_path, TOOL)
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
                               passing a file. The file groups properties by category under a
                               section named after the engine that emits them, for example
                               `{ jaspergold: { unreachable: [ prop1, prop2 ] } }`. A file whose
                               categories sit at the top level with no section applies to every
                               engine.'''))

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
