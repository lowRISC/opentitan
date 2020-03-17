# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Command-line tool to parse and process testplan Hjson into a data structure
    The data structure is used for expansion inline within DV plan documentation
    as well as for annotating the regression results.
"""
import logging as log
import os
import sys
from pathlib import PurePath

import hjson
import mistletoe
from tabulate import tabulate

from .class_defs import *


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
            if key == "name": name = obj[key]
            substitutions.append({key: obj[key]})
    for imported_testplan in imported_testplans:
        obj = merge_dicts(
            obj, parse_hjson(os.path.join(repo_root, imported_testplan)))

    testplan = Testplan(name=name)
    for entry in obj["entries"]:
        if not TestplanEntry.is_valid_entry(entry): sys.exit(1)
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
    if not "test_results" in obj.keys():
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
    '''merge 2 dicts into one

    This funciton takes 2 dicts as args list1 and list2. It recursively merges list2 into
    list1 and returns list1. The recursion happens when the the value of a key in both lists
    is a dict. If the values of the same key in both lists (at the same tree level) are of
    dissimilar type, then there is a conflict and an error is thrown. If they are of the same
    scalar type, then the third arg "use_list1_for_defaults" is used to pick the final one.
    '''
    for key in list2.keys():
        if key in list1:
            if type(list1[key]) is list and type(list2[key]) is list:
                list1[key].extend(list2[key])
            elif type(list1[key]) is dict and type(list2[key]) is dict:
                list1[key] = merge_dicts(list1[key], list2[key])
            elif (type(list1[key]) == type(list2[key])):
                if not use_list1_for_defaults:
                    list1[key] = list2[key]
            else:
                print("The type of value of key \"", key, "\" in list1: \"", \
                      str(type(list1[key])), \
                      "\" does not match the type of value in list2: \"", \
                      str(type(list2[key])), \
                      "\". The two lists cannot be merged.")
                sys.exit(1)
        else:
            list1[key] = list2[key]
    return list1


def gen_html(testplan_file, regr_results_file, outbuf):
    testplan = parse_testplan(os.path.abspath(testplan_file))
    if regr_results_file:
        regr_results = parse_regr_results(os.path.abspath(regr_results_file))
        gen_html_regr_results_table(testplan, regr_results, outbuf)
    else:
        gen_html_testplan_table(testplan, outbuf)
    outbuf.write('\n')
