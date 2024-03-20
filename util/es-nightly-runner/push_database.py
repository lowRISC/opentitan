#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Push result data to a database.
"""

import sqlite3


class DBError(Exception):
    pass


class TestResultPusher:
    def __init__(
        self, database, table_name_execs, table_name_testcases, table_name_testnames
    ):
        """
        Push the results to a database using the given table names.

        @param database:             The database object to push to
        @param table_name_execs:     Table name for executions
        @param table_name_testcases: Table name for test cases
        @param table_name_testnames: Table name for test names
        """
        self.connection = database
        self.table_name_execs = table_name_execs
        self.table_name_testnames = table_name_testnames
        self.table_name_testcases = table_name_testcases

    def execute(self, sql):
        try:
            c = self.connection.cursor()
            c.execute(sql)
        except sqlite3.Error as exc:
            raise DBError(str(exc)) from exc

    def create_tables(self):
        """
        Ensure that the tables for the data exist.
        """

        # The executions table
        sql = """\
CREATE TABLE {} IF NOT EXISTS (
    id INTEGER PRIMARY KEY,
    timestamp NOT NULL, -- a unix epoch time object
    hostname VARCHAR(256)
);
""".format(
            self.table_name_execs
        )
        self.execute(sql)

        # The test names table
        sql = """\
CREATE TABLE {} IF NOT EXISTS (
    id INTEGER PRIMARY KEY,
    name VARCHAR(256) UNIQUE
);
""".format(
            self.table_name_testnames
        )
        self.execute(sql)

        # The test cases table
        sql = """\
CREATE TABLE {} IF NOT EXISTS (
    id INTEGER,
    name_id INTEGER NOT NULL,
    duration REAL NOT NULL,
    result VARCHAR(8), # Passed, Failed, Skipped, Errored
    FOREIGN KEY(name_id) REFERENCES {}(id)
);
""".format(
            self.table_name_testcases, self.table_name_testnames
        )
        self.execute(sql)
