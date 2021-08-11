#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script provides common DV simulation specific utilities.
"""

import re
from collections import OrderedDict


# Capture the summary results as a list of lists.
# The text coverage report is passed as input to the function, in addition to
# the tool used. The tool returns a 2D list if the coverage report file was read
# and the coverage was extracted successfully. It returns a tuple of:
#   List of metrics and values
#   Final coverage total
#
# Raises the appropriate exception if the coverage summary extraction fails.
def get_cov_summary_table(cov_report_txt, tool):
    with open(cov_report_txt, 'r') as f:
        if tool == 'xcelium':
            return xcelium_cov_summary_table(f)
        if tool == 'vcs':
            return vcs_cov_summary_table(f)
        raise NotImplementedError(f"{tool} is unsupported for cov extraction.")


# Same desc as above, but specific to Xcelium and takes an opened input stream.
def xcelium_cov_summary_table(buf):
    for line in buf:
        if "name" in line:
            # Strip the line and remove the unwanted "* Covered" string.
            metrics = line.strip().replace("* Covered", "").split()
            # Change first item to 'Score'.
            metrics[0] = 'Score'

            # Gather the list of metrics.
            items = OrderedDict()
            for metric in metrics:
                items[metric] = {}
                items[metric]['covered'] = 0
                items[metric]['total'] = 0

            # Next line is a separator.
            line = buf.readline()

            # Subsequent lines are coverage items to be aggregated.
            for line in buf:
                line = re.sub(r"%\s+\(", "%(", line)
                values = line.strip().split()
                for i, value in enumerate(values):
                    value = value.strip()
                    m = re.search(r"\((\d+)/(\d+).*\)", value)
                    if m:
                        items[metrics[i]]['covered'] += int(m.group(1))
                        items[metrics[i]]['total'] += int(m.group(2))
                        items['Score']['covered'] += int(m.group(1))
                        items['Score']['total'] += int(m.group(2))
            # Capture the percentages and the aggregate.
            values = []
            cov_total = None
            for metric in items.keys():
                if items[metric]['total'] == 0:
                    values.append("-- %")
                else:
                    value = items[metric]['covered'] / items[metric][
                        'total'] * 100
                    value = "{0:.2f} %".format(round(value, 2))
                    values.append(value)
                    if metric == 'Score':
                        cov_total = value
            return [items.keys(), values], cov_total

    # If we reached here, then we were unable to extract the coverage.
    raise SyntaxError(f"Coverage data not found in {buf.name}!")


# Same desc as above, but specific to VCS and takes an opened input stream.
def vcs_cov_summary_table(buf):
    for line in buf:
        match = re.match("total coverage summary", line, re.IGNORECASE)
        if match:
            # Metrics on the next line.
            line = buf.readline().strip()
            metrics = line.split()
            # Values on the next.
            line = buf.readline().strip()
            # Pretty up the values - add % sign for ease of post
            # processing.
            values = []
            for val in line.split():
                val += " %"
                values.append(val)
            # first row is coverage total
            cov_total = values[0]
            return [metrics, values], cov_total

    # If we reached here, then we were unable to extract the coverage.
    raise SyntaxError(f"Coverage data not found in {buf.name}!")
