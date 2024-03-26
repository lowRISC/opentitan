#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Parser for the Open Titan test result files.

The test result files are supplied as JUnitXML, which has test cases named in a particular way.
We can process this and extract the content so that it is able to be processed into our data
collection systems.

The JUnitXML is in a slightly different format to that expected by the junitparser library.
The format used by the bazel output is (approximately)

    <testsuites>
        <testsuite>
            <testcase>
                <error>
            <testcase>
            <system-out>
                CDATA
            </system-out>
        </testsuite>
    </testsuites>

Whereas the junitparser expects the <system-out> to be present within the testcase, for it to
be accessible.
"""

import datetime
import os
import socket

import junitparser

from results import Results, Result, State


# Configuration for the module

# Should we change the name of the testcase in what we write out in the JUnitXML ?
MODIFY_TEST_NAME_IN_JUNITXML = True


class JUnitNotRecognisedError(Exception):
    """
    If we didn't understand the JUnitXML this error is raised.
    """

    pass


class OTJUnitXML:
    def __init__(self, filename):
        self.filename = filename
        self._junitxml = None
        self._results = None

    @property
    def junitxml(self):
        if self._junitxml is None:
            try:
                self._junitxml = junitparser.JUnitXml.fromfile(self.filename)
            except junitparser.junitparser.JUnitXmlError as exc:
                raise JUnitNotRecognisedError(
                    "JUnitXML not recognised: {}".format(exc)
                ) from exc

            # Fix up the JUnit XML by moving the output around.
            suites = list(self._junitxml)
            for suite in suites:
                # Move the system-data at the suite level to the test level.
                # (only for the first test)
                tests = list(suite)
                system_out = suite._elem.find("system-out")
                if system_out is not None:
                    test = tests[0]
                    # Add the system-out to the test element
                    test._elem.append(system_out)
                    suite._elem.remove(system_out)

                if MODIFY_TEST_NAME_IN_JUNITXML:
                    for test in tests:
                        test.name = self.bazel_name(test.name)

        return self._junitxml

    def bazel_name(self, name):
        """
        Convert the unit test name to the Bazel specification name.
        """
        if not name.startswith("//"):
            # We only manipulate the test name if it does not start with a //.
            name = "//" + name
            if name.endswith(".bash"):
                name = name[:-5]
            (left, right) = name.rsplit("/", 1)
            name = "{}:{}".format(left, right)
        return name

    @property
    def timestamp(self):
        return self.junitxml.timestamp

    @timestamp.setter
    def timestamp(self, value):
        self.junitxml.timestamp = value

    @property
    def results(self):
        """
        Turn the JUnitXML into a Results object.
        """
        if not self._results:
            self._results = Results()

            suites = list(self.junitxml)
            for suite in suites:
                for test in suite:
                    name = self.bazel_name(test.name)
                    if test.is_skipped:
                        state = State.SKIPPED
                    elif test.is_passed:
                        state = State.PASSED
                    else:
                        # Error is not reported in the junitparser library, so we need to do this
                        # ourselves.
                        state = State.FAILED
                        for res in test.result:
                            if isinstance(res, junitparser.Error):
                                state = State.ERRORED
                    duration = test.time
                    output = test.system_out

                    result = Result(name, state, duration, output)
                    self._results.tests.append(result)

        return self._results

    def ntests(self):
        return self.results.ntests


class OTDir:
    def __init__(self, path, collection_date=None):
        """
        OpenTitan results directory parser.

        @param path:            Path to the bazel-out directory to parse test results from
        @param collection_date: Datetime that the data was collected to populate into results,
                                or None to use today
        """
        self.path = path
        all_results = Results()
        all_junitxml = []

        if collection_date is None:
            self.timestamp = None
            self.timestamp_datetime = None
        elif isinstance(collection_date, datetime.datetime):
            # Turn into ISO 8601 formatted time string if we're given a datetime.
            self.timestamp_datetime = collection_date
            self.timestamp = collection_date.isoformat()
        else:
            # Ensure that collection date is a datetime, and that timestamp is a ISO 8601 string
            self.timestamp = collection_date
            self.timestamp_datetime = datetime.datetime.fromisoformat(collection_date)

        all_results.timestamp = self.timestamp

        print("Scanning for test files in %s" % (self.path,))
        for dir_path, dir_names, file_names in os.walk(self.path):
            # Ensure that we walk down the directories in a known order
            dir_names.sort()

            # The only file we care about is 'test.xml' at present - if there are other XML files
            # present, we will ignore them as they're almost certainly not JUnitXML.
            test_file = os.path.join(dir_path, "test.xml")
            if os.path.exists(test_file):
                print("Processing %s" % (test_file,))
                try:
                    testxml = OTJUnitXML(test_file)
                    if collection_date:
                        # Override the timestamp (or supply one) if one was given.
                        testxml.timestamp = self.timestamp
                    else:
                        if testxml.timestamp:
                            # If we didn't have a timestamp, populate it from the read data
                            self.timestamp = testxml.timestamp
                            self.timestamp_datetime = datetime.datetime.fromisoformat(
                                testxml.timestamp
                            )

                    results = testxml.results
                except JUnitNotRecognisedError as exc:
                    # If we don't recognise the JUnitXML, we'll just skip this file
                    print("Skipping XML file '%s': %s" % (test_file, exc))
                    continue
                all_junitxml.append(testxml)
                all_results.tests.extend(results.tests)

        self.all_junitxml = all_junitxml
        self.all_results = all_results

    def ntests(self):
        """
        Retrieve the total number of tests.
        """
        return self.all_results.ntests

    def write(
        self, output, flatten_testsuites=False, add_hostname=False, add_properties=None
    ):
        """
        Write out an amalgamated JUnitXML file.

        @param output:              The file to write the JUnitXML file to
        @param flatten_testsuites:  Flatten the test suites to just one test suite
        @param properties:          Properties to set as a dictionary; use a value
                                    of None to delete.
        """

        def modify_suite(suite):
            if add_hostname:
                suite.hostname = socket.getaddrinfo(
                    socket.gethostname(), 0, flags=socket.AI_CANONNAME
                )[0][3]
            if add_properties:
                for key, value in add_properties.items():
                    if value is None:
                        suite.remove_property(key)
                    else:
                        suite.add_property(key, str(value))

        xml = junitparser.JUnitXml()
        if flatten_testsuites:
            # Produce a file that has only a single test suite containing all the tests
            print("Flattening suites")
            ts = junitparser.TestSuite(name="OpenTitan test results")
            modify_suite(ts)
            for otjunitxml in self.all_junitxml:
                if not ts.timestamp:
                    ts.timestamp = otjunitxml.timestamp
                for suite in otjunitxml.junitxml:
                    for test in suite:
                        ts.add_testcase(test)
            xml.add_testsuite(ts)

        else:
            # Produce a file that has many test suites, each containing a single test
            for otjunitxml in self.all_junitxml:
                for suite in otjunitxml.junitxml:
                    modify_suite(suite)
                    if not suite.timestamp:
                        suite.timestamp = otjunitxml.timestamp
                    xml.add_testsuite(suite)
        xml.write(output)


if __name__ == "__main__":
    bazel_out_dir = "bazel-out/"

    otdir = OTDir(bazel_out_dir)

    for result in otdir.all_results:
        print("Test '%s': state=%s" % (result.name, result.state))
