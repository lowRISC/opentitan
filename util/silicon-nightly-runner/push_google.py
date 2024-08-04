#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Push data to a google sheet
"""

import datetime
import re
import gspread
import bazel_report

SERVICE_FILE = "service-account.json"
USER_FILE = "user-account.json"


def continuous_sequences(numbers):
    """
    Turn a list of numbers into a list of lists of continuous sequences.

    For example the number sequence [1,2,3,5,6] would be turned into [[1,2,3], [5,6]].
    """
    numbers = sorted(numbers)
    sequences = []
    sequence = []
    last_number = None
    for number in numbers:
        if last_number is not None and last_number + 1 != number:
            sequences.append(sequence)
            sequence = []

        sequence.append(number)
        last_number = number
    if sequence:
        sequences.append(sequence)

    return sequences


def column_name(column):
    column -= 1
    if column < 26:
        return chr(65 + column)
    else:
        return chr(65 + (column // 26) -1 ) + chr(65 + (column % 26))


def cell_name(row, column):
    return column_name(column) + str(row)


class CoalescingSheetUpdater:
    """
    Update a Google sheet with random access to cells, coalescing requests.

    The Google sheet API has a rate limit on the number of write operations that can be applied
    per minute. We want to be able to use random access to write to the cells, and then apply
    the changes to the sheet em masse.
    """

    def __init__(self, sheet):
        self.sheet = sheet

        # For the operations we're doing, we focus on updating columns of data in chunks
        # when the changes are committed
        self.update_columns = {}

    def update_cell(self, y, x, value):
        """
        Update a cell in our list of updates to apply.
        """
        if x not in self.update_columns:
            self.update_columns[x] = {}
        self.update_columns[x][y] = value

    def commit(self):
        """
        Commit the cell updates that have been applied on a per-column basis.
        """
        for x, column in self.update_columns.items():
            # Each column may have discontinuous regions that are being updated
            # We need to separate out the updates into regions that are continuous
            # so that we can update the region in one go.
            rows = column.keys()
            for group in continuous_sequences(rows):
                # Each group is a set of rows that makes up a continuous sequence
                values = [[column[row]] for row in group]
                cell_range = "{}:{}".format(
                    cell_name(group[0], x), cell_name(group[-1], x)
                )
                print("Cells %s = %r" % (cell_range, values))
                self.sheet.update(range_name=cell_range, values=values)


class TestResultPusher:
    def __init__(
        self,
        gcreds,
        sheet_id,
        sheet_tab,
        row_offset=1,
        column_offset=2,
        test_name_column=1,
    ):
        self.gcreds = gcreds
        self.sheet_id = sheet_id
        self.sheet_tab = sheet_tab
        self.row_offset = row_offset
        self.column_offset = column_offset
        self.test_name_column = test_name_column
        self.test_name_rows = {}
        self.test_name_last_row = self.row_offset - 1

    def push(self, junit_file, date=None):
        sh = self.gcreds.open_by_key(self.sheet_id)

        sheet = None
        try:
            sheet = sh.worksheet(self.sheet_tab)
        except gspread.WorksheetNotFound:
            sheet = sh.add_worksheet(self.sheet_tab, rows=1000, cols=200)

        updater = CoalescingSheetUpdater(sheet)
        self.get_test_names(sheet)

        suites = bazel_report.OTJUnitXML(junit_file)

        # If no result date was supplied, we use today
        if date:
            date = date.date()
        # FIX-ME: Use suites.timestamp instead.
        elif list(suites.junitxml)[0].timestamp:
            date = datetime.datetime.strptime(
                list(suites.junitxml)[0].timestamp, "%Y-%m-%dT%H:%M:%S"
            ).date()
        else:
            date = datetime.date.today()
        start = self.start_date(sheet)
        delta = date - start
        column = max(0, delta.days)

        # Update the date entry as a heading (if there is space)
        if self.row_offset > 1:
            updater.update_cell(
                self.row_offset - 1, column + self.column_offset, date.isoformat()
            )
        for result in suites.results:
            value = result.state.value
            row = self.test_name_rows.get(result.name, None)
            if not row:
                # This test isn't known to the table, so we need to add it as a new row
                self.test_name_last_row += 1
                row = self.test_name_last_row
                print("No test name found for %s, need to add to rows" % (result.name,))
                updater.update_cell(row, self.test_name_column, result.name)

            updater.update_cell(row, column + self.column_offset, value)

        updater.commit()

    def start_date(self, sheet):
        """
        Obtain the first date within the sheet, if can't find then returns today.
        """
        columns = self.get_column_names(sheet)
        columns = [] if len(columns) == 0 else columns[0]
        pattern = re.compile(r"\d{4}-\d{2}-\d{2}")
        for column in columns:
            matches = pattern.findall(column)
            if matches:
                return datetime.date.fromisoformat(column)
        return datetime.date.today()

    def get_test_names(self, sheet):
        """
        Obtain a list of the test names and their rows within the sheet.
        """
        row_chunks = 100
        row_base = self.row_offset
        while True:
            cell_range = "{}:{}".format(
                cell_name(row_base, self.test_name_column),
                cell_name(row_base + row_chunks - 1, self.test_name_column),
            )
            cells = sheet.get_values(cell_range)
            done = len(cells) < row_chunks
            for offset, cell in enumerate(cells):
                row = row_base + offset
                if len(cell) == 0:
                    done = True
                    continue
                value = cell[0]
                if not value:
                    done = True
                else:
                    print("Test '%s' is row %i" % (value, row))
                    if self.test_name_rows.get(value):
                        print(
                            "WARNING: The row '%s' is present multiple times in the sheet"
                            % (value,)
                        )
                    self.test_name_rows[value] = row
                    self.test_name_last_row = row
            if done:
                break
            row_base += row_chunks

    def get_column_names(self, sheet):
        """
        Obtain a list of column names within the sheet.
        """
        row_base = 1
        cell_range = "{}:{}".format(
            cell_name(row_base, self.test_name_column),
            cell_name(row_base, self.test_name_column + 50),
        )

        return sheet.get_values(cell_range)
