#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""TestplanEntry and Testplan classes for maintaining testplan entries
"""

import re
import sys


class TestplanEntry():
    """An entry in the testplan

    A testplan entry has the following information: name of the planned test (testpoint),
    a brief description indicating intent, stimulus and checking procedure, targeted milestone
    and the list of actual developed tests.
    """
    name = ""
    desc = ""
    milestone = ""
    tests = []

    fields = ("name", "desc", "milestone", "tests")
    milestones = ("na", "v1", "v2", "v3")

    def __init__(self, name, desc, milestone, tests, substitutions=[]):
        self.name = name
        self.desc = desc
        self.milestone = milestone
        self.tests = tests
        if not self.do_substitutions(substitutions): sys.exit(1)

    @staticmethod
    def is_valid_entry(kv_pairs):
        '''Pass a list of key=value pairs to check if testplan entries can be extracted
        from it.
        '''
        for field in TestplanEntry.fields:
            if not field in kv_pairs.keys():
                print(
                    "Error: input key-value pairs does not contain all of the ",
                    "required fields to create an entry:\n", kv_pairs,
                    "\nRequired fields:\n", TestplanEntry.fields)
                return False
            if type(kv_pairs[field]) is str and kv_pairs[field] == "":
                print("Error: field \'", field, "\' is an empty string\n:",
                      kv_pairs)
                return False
            if field == "milestone" and kv_pairs[
                    field] not in TestplanEntry.milestones:
                print("Error: milestone \'", kv_pairs[field],
                      "\' is invalid. Legal values:\n",
                      TestplanEntry.milestones)
                return False
        return True

    def do_substitutions(self, substitutions):
        '''Substitute {wildcards} in tests

        If tests have {wildcards}, they are substituted with the 'correct' values using
        key=value pairs provided by the substitutions arg. If wildcards are present but no
        replacement is available, then the wildcards are replaced with an empty string.
        '''
        if substitutions == []: return True
        for kv_pair in substitutions:
            resolved_tests = []
            [(k, v)] = kv_pair.items()
            for test in self.tests:
                match = re.findall(r"{([A-Za-z0-9\_]+)}", test)
                if len(match) > 0:
                    # match is a list of wildcards used in test
                    for item in match:
                        if item == k:
                            if type(v) is list:
                                if v == []:
                                    resolved_test = test.replace(
                                        "{" + item + "}", "")
                                    resolved_tests.append(resolved_test)
                                else:
                                    for subst_item in v:
                                        resolved_test = test.replace(
                                            "{" + item + "}", subst_item)
                                        resolved_tests.append(resolved_test)
                            elif type(v) is str:
                                resolved_test = test.replace(
                                    "{" + item + "}", v)
                                resolved_tests.append(resolved_test)
                            else:
                                print(
                                    "Error: wildcard", item, "in test", test,
                                    "has no viable",
                                    "replacement value (need str or list):\n",
                                    kv_pair)
                                return False
                else:
                    resolved_tests.append(test)
            if resolved_tests != []: self.tests = resolved_tests

        # if wildcards have no available replacements in substitutions arg, then
        # replace with empty string
        resolved_tests = []
        for test in self.tests:
            match = re.findall(r"{([A-Za-z0-9\_]+)}", test)
            if len(match) > 0:
                for item in match:
                    resolved_tests.append(test.replace("{" + item + "}", ""))
        if resolved_tests != []: self.tests = resolved_tests
        return True

    def map_regr_results(self, regr_results):
        '''map regression results to tests in this entry

        Given a list of regression results (a tuple containing {test name, # passing and
        # total} find if the name of the test in the results list matches the written tests
        in this testplan entry. If there is a match, then append the passing / total
        information. If no match is found, or if self.tests is an empty list, indicate 0/1
        passing so that it is factored into the final total.
        '''
        test_results = []
        for test in self.tests:
            found = False
            for regr_result in regr_results:
                if test == regr_result["name"]:
                    test_results.append(regr_result)
                    regr_result["mapped"] = True
                    found = True
                    break

            # if a test was not found in regr results, indicate 0/1 passing
            if not found:
                test_results.append({"name": test, "passing": 0, "total": 1})

        # if no written tests were indicated in the testplan, reuse planned
        # test name and indicate 0/1 passing
        if self.tests == []:
            test_results.append({"name": self.name, "passing": 0, "total": 1})

        # replace tests with test results
        self.tests = test_results
        return regr_results

    def display(self):
        print("testpoint: ", self.name)
        print("description: ", self.desc)
        print("milestone: ", self.milestone)
        print("tests: ", self.tests)


class Testplan():
    """The full testplan

    This comprises of TestplanEntry entries
    """

    name = ""
    entries = []

    def __init__(self, name):
        self.name = name
        self.entries = []
        if name == "":
            print("Error: testplan name cannot be empty")
            sys.exit(1)

    def entry_exists(self, entry):
        '''check if new entry has the same name as one of the existing entries
        '''
        for existing_entry in self.entries:
            if entry.name == existing_entry.name:
                print("Error: found a testplan entry with name = ", entry.name)
                print("existing entry:\n", existing_entry)
                print("new entry:\n", entry)
                return True
        return False

    def add_entry(self, entry):
        '''add a new entry into the testplan
        '''
        if self.entry_exists(entry): sys.exit(1)
        self.entries.append(entry)

    def sort(self):
        '''sort entries by milestone
        '''
        self.entries = sorted(self.entries, key=lambda entry: entry.milestone)

    def map_regr_results(self, regr_results):
        '''map regression results to testplan entries
        '''

        def sum_results(totals, entry):
            '''function to generate milestone and grand totals
            '''
            ms = entry.milestone
            for test in entry.tests:
                totals[ms].tests[0]["passing"] += test["passing"]
                totals[ms].tests[0]["total"] += test["total"]
            return totals

        totals = {}
        for ms in TestplanEntry.milestones:
            name = "<ignore>"
            totals[ms] = TestplanEntry(
                name=name,
                desc=name,
                milestone=ms,
                tests=[{
                    "name": "TOTAL",
                    "passing": 0,
                    "total": 0
                }])

        for entry in self.entries:
            regr_results = entry.map_regr_results(regr_results)
            totals = sum_results(totals, entry)

        # extract unmapped tests from regr_results and create 'unmapped' entry
        unmapped_regr_results = []
        for regr_result in regr_results:
            if not "mapped" in regr_result.keys():
                unmapped_regr_results.append(regr_result)

        unmapped = TestplanEntry(
            name="Unmapped tests",
            desc="Unmapped tests",
            milestone="na",
            tests=unmapped_regr_results)
        totals = sum_results(totals, unmapped)

        # add the grand total: "na" key used for grand total
        for ms in TestplanEntry.milestones:
            if ms != "na":
                totals["na"].tests[0]["passing"] += totals[ms].tests[0][
                    "passing"]
                totals["na"].tests[0]["total"] += totals[ms].tests[0]["total"]

        # add total back into 'entries'
        for key in totals.keys():
            if key != "na": self.entries.append(totals[key])
        self.sort()
        self.entries.append(unmapped)
        self.entries.append(totals["na"])

    def display(self):
        '''display the complete testplan for debug
        '''
        print("name: ", self.name)
        for entry in self.entries:
            entry.display()
