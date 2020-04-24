# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to parse and process testplan Hjson into a data structure
    The data structure is used for expansion inline within DV plan documentation
    as well as for annotating the regression results.
"""
import os
import sys

import hjson
import mistletoe
from tabulate import tabulate

from .class_defs import Testplan, TestplanEntry


def parse_testplan(filename):
    '''Parse testplan Hjson file into a datastructure'''
    self_path = os.path.dirname(os.path.realpath(__file__))
    repo_root = os.path.abspath(os.path.join(self_path, os.pardir, os.pardir, os.pardir))

    name = ""
    imported_testplans = []
    substitutions = []
    obj = parse_hjson(filename)
    for key in obj.keys():
        if key == "import_testplans":
            imported_testplans = obj[key]
        elif key != "entries":
            if key == "name":
                name = obj[key]
            substitutions.append({key: obj[key]})
    for imported_testplan in imported_testplans:
        obj = merge_dicts(
            obj, parse_hjson(os.path.join(repo_root, imported_testplan)))

    testplan = Testplan(name=name)
    for entry in obj["entries"]:
        if not TestplanEntry.is_valid_entry(entry):
            sys.exit(1)
        testplan_entry = TestplanEntry(name=entry["name"],
                                       desc=entry["desc"],
                                       milestone=entry["milestone"],
                                       tests=entry["tests"],
                                       substitutions=substitutions)
        testplan.add_entry(testplan_entry)
    testplan.sort()
    return testplan


def gen_html_indent(lvl):
    return "    " * lvl


def gen_html_write_style(outbuf):
    outbuf.write("<style>\n")
    outbuf.write("table.dv {\n")
    outbuf.write("    border: 1px solid black;\n")
    outbuf.write("    border-collapse: collapse;\n")
    outbuf.write("    text-align: left;\n")
    outbuf.write("    vertical-align: middle;\n")
    outbuf.write("    display: table;\n")
    outbuf.write("}\n")
    outbuf.write("th, td {\n")
    outbuf.write("    border: 1px solid black;\n")
    outbuf.write("}\n")
    outbuf.write("</style>\n")


def gen_html_testplan_table(testplan, outbuf):
    '''generate HTML table from testplan with the following fields
    milestone, planned test name, description
    '''

    text = testplan.testplan_table(fmt="html")
    text = text.replace("<table>", "<table class=\"dv\">")
    gen_html_write_style(outbuf)
    outbuf.write(text)
    return


def gen_html_regr_results_table(testplan, regr_results, outbuf):
    '''map regr results to testplan and create a table with the following fields
    milestone, planned test name, actual written tests, pass/total
    '''
    text = "# Regression Results\n"
    text += "## Run on{}\n".format(regr_results["timestamp"])
    text += "### Test Results\n\n"
    text += testplan.results_table(regr_results["test_results"])
    if "cov_results" in regr_results.keys():
        text += "\n### Coverage Results\n\n"
        cov_header = []
        cov_values = []
        for cov in regr_results["cov_results"]:
            cov_header.append(cov["name"])
            cov_values.append(str(cov["result"]))
        colalign = (("center", ) * len(cov_header))
        text += tabulate([cov_header, cov_values],
                         headers="firstrow",
                         tablefmt="pipe",
                         colalign=colalign)
    text = mistletoe.markdown(text)
    text = text.replace("<table>", "<table class=\"dv\">")
    gen_html_write_style(outbuf)
    outbuf.write(text)
    return


def parse_regr_results(filename):
    obj = parse_hjson(filename)
    # TODO need additional syntax checks
    if "test_results" not in obj.keys():
        print("Error: key \'test_results\' not found")
        sys, exit(1)
    return obj


def parse_hjson(filename):
    try:
        f = open(str(filename), 'rU')
        text = f.read()
        odict = hjson.loads(text)
        return odict
    except IOError:
        print('IO Error:', filename)
        raise SystemExit(sys.exc_info()[1])
    except hjson.scanner.HjsonDecodeError as e:
        print("Error: Unable to decode HJSON file %s: %s" %
              (str(filename), str(e)))
        sys.exit(1)


def merge_dicts(list1, list2, use_list1_for_defaults=True):
    '''Merge 2 dicts into one

    This function takes 2 dicts as args list1 and list2. It recursively merges list2 into
    list1 and returns list1. The recursion happens when the the value of a key in both lists
    is a dict. If the values of the same key in both lists (at the same tree level) are of
    dissimilar type, then there is a conflict and an error is thrown. If they are of the same
    scalar type, then the third arg "use_list1_for_defaults" is used to pick the final one.
    '''
    for key, item2 in list2.items():
        item1 = list1.get(key)
        if item1 is None:
            list1[key] = item2
            continue

        # Both dictionaries have an entry for this key. Are they both lists? If
        # so, append.
        if isinstance(item1, list) and isinstance(item2, list):
            list1[key] = item1 + item2
            continue

        # Are they both dictionaries? If so, recurse.
        if isinstance(item1, dict) and isinstance(item2, dict):
            merge_dicts(item1, item2)
            continue

        # We treat other types as atoms. If the types of the two items are
        # equal pick one or the other (based on use_list1_for_defaults).
        if isinstance(item1, type(item2)) and isinstance(item2, type(item1)):
            list1[key] = item1 if use_list1_for_defaults else item2
            continue

        # Oh no! We can't merge this.
        print("ERROR: Cannot merge dictionaries at key {!r} because items have "
              "conflicting types ({} in 1st; {} in 2nd)."
              .format(type(item1), type(item2)))
        sys.exit(1)

    return list1


def gen_html(testplan_file, regr_results_file, outbuf):
    testplan = parse_testplan(os.path.abspath(testplan_file))
    if regr_results_file:
        regr_results = parse_regr_results(os.path.abspath(regr_results_file))
        gen_html_regr_results_table(testplan, regr_results, outbuf)
    else:
        gen_html_testplan_table(testplan, outbuf)
    outbuf.write('\n')
