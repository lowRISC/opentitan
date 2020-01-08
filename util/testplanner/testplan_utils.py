#!/usr/bin/env python3
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

from .class_defs import *


def parse_testplan(filename):
    '''Parse testplan Hjson file into a datastructure'''
    self_path = os.path.dirname(os.path.realpath(__file__))
    repo_root = os.path.abspath(os.path.join(self_path, os.pardir, os.pardir))

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
    outbuf.write("    width: 100%;\n")
    outbuf.write("    text-align: center;\n")
    outbuf.write("    vertical-align: middle;\n")
    outbuf.write("    margin-left: auto;;\n")
    outbuf.write("    margin-right: auto;;\n")
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
    def print_row(ms, name, desc, tests, cell, outbuf):
        cellb = "<" + cell + ">"
        celle = "</" + cell + ">"
        tests_str = ""
        if cell == "td":
            # remove leading and trailing whitespaces
            desc = mistletoe.markdown(desc.strip())
            tests_str = "<ul>\n"
            for test in tests:
                tests_str += "<li>" + str(test) + "</li>\n"
            tests_str += "</ul>"
        else:
            tests_str = tests

        outbuf.write(gen_html_indent(1) + "<tr>\n")
        outbuf.write(gen_html_indent(2) + cellb + ms + celle + "\n")
        outbuf.write(gen_html_indent(2) + cellb + name + celle + "\n")

        # make description text left aligned
        cellb_desc = cellb
        if cell == "td":
            cellb_desc = cellb_desc[:-1] + " style=\"text-align: left\"" + ">"
        outbuf.write(gen_html_indent(2) + cellb_desc + desc + celle + "\n")
        outbuf.write(gen_html_indent(2) + cellb + tests_str + celle + "\n")
        outbuf.write(gen_html_indent(1) + "</tr>\n")

    gen_html_write_style(outbuf)
    outbuf.write("<table class=\"dv\">\n")
    print_row("Milestone", "Name", "Description", "Tests", "th", outbuf)
    for entry in testplan.entries:
        print_row(entry.milestone, entry.name, entry.desc, entry.tests, "td",
                  outbuf)
    outbuf.write("</table>\n")
    return


def gen_html_regr_results_table(testplan, regr_results, outbuf):
    '''map regr results to testplan and create a table with the following fields
    milestone, planned test name, actual written tests, pass/total
    '''
    def print_row(ms, name, tests, results, cell, outbuf):
        cellb = "<" + cell + ">"
        celle = "</" + cell + ">"
        tests_str = ""
        results_str = ""
        if cell == "td":
            for test in tests:
                if tests_str != "": tests_str += "<br>"
                if results_str != "": results_str += "<br>"
                tests_str += str(test["name"])
                results_str += str(test["passing"]) + "/" + str(test["total"])
        else:
            tests_str = tests
            results_str = results
        if ms == "N.A.": ms = ""
        if name == "N.A.":
            name = ""
            tests_str = "<strong>" + tests_str + "</strong>"
            results_str = "<strong>" + results_str + "</strong>"

        outbuf.write(gen_html_indent(1) + "<tr>\n")
        outbuf.write(gen_html_indent(2) + cellb + ms + celle + "\n")
        outbuf.write(gen_html_indent(2) + cellb + name + celle + "\n")
        outbuf.write(gen_html_indent(2) + cellb + tests_str + celle + "\n")
        outbuf.write(gen_html_indent(2) + cellb + results_str + celle + "\n")
        outbuf.write(gen_html_indent(1) + "</tr>\n")

    testplan.map_regr_results(regr_results["test_results"])

    gen_html_write_style(outbuf)
    outbuf.write("<h1 style=\"text-align: center\" " + "id=\"" +
                 testplan.name + "-regression-results\">" +
                 testplan.name.upper() + " Regression Results</h1>\n")

    outbuf.write("<h2 style=\"text-align: center\">" + "Run on " +
                 regr_results["timestamp"] + "</h2>\n")

    # test results
    outbuf.write("<h3 style=\"text-align: center\">Test Results</h2>\n")
    outbuf.write("<table class=\"dv\">\n")
    print_row("Milestone", "Name", "Tests", "Results", "th", outbuf)
    for entry in testplan.entries:
        print_row(entry.milestone, entry.name, entry.tests, None, "td", outbuf)
    outbuf.write("</table>\n")

    # coverage results
    outbuf.write("<h3 style=\"text-align: center\">Coverage Results</h2>\n")
    outbuf.write("<table class=\"dv\">\n")
    outbuf.write(gen_html_indent(1) + "<tr>\n")
    # title
    outbuf.write(gen_html_indent(1) + "<tr>\n")
    for cov in regr_results["cov_results"]:
        outbuf.write(
            gen_html_indent(2) + "<th>" + cov["name"].capitalize() + "</th>\n")
    outbuf.write(gen_html_indent(1) + "</tr>\n")
    # result
    outbuf.write(gen_html_indent(1) + "<tr>\n")
    for cov in regr_results["cov_results"]:
        outbuf.write(
            gen_html_indent(2) + "<td>" + str(cov["result"]) + "</td>\n")
    outbuf.write(gen_html_indent(1) + "</tr>\n")
    outbuf.write("</table>\n")
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
        print("Error: Unable to decode HJSON file %s: %s" % (str(filename), str(e)))
        sys.exit(1)


def merge_dicts(list1, list2):
    '''merge 2 dicts into one

    This funciton takes 2 dicts as args list1 and list2. It recursively merges list2 into
    list1 and returns list1. The recursion happens when the the value of a key in both lists
    is a dict. If the values of the same key in both lists (at the same tree level) are of
    type str (or of dissimilar type) then there is a conflict, and and error is thrown.
    '''
    for key in list2.keys():
        if key in list1:
            if type(list1[key]) is list and type(list2[key]) is list:
                list1[key].extend(list2[key])
            elif type(list1[key]) is dict and type(list2[key]) is dict:
                list1[key] = merge_dicts(list1[key], list2[key])
            else:
                print("The type of value of key ", key, "in list1: ", str(type(list1[key])), \
                      " does not match the type of value in list2: ", str(type(list2[key])), \
                      " or they are not of type list or dict. The two lists cannot be merged.")
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
