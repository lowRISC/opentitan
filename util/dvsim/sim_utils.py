#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
This script provides common DV simulation specific utilities.
"""

import re
from collections import OrderedDict
from typing import List, Tuple


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


def get_job_runtime(log_text: List, tool: str) -> Tuple[float, str]:
    """Returns the job runtime (wall clock time) along with its units.

    EDA tools indicate how long the job ran in terms of CPU time in the log
    file. This method invokes the tool specific method which parses the log
    text and returns the runtime as a floating point value followed by its
    units as a tuple.

    `log_text` is the job's log file contents as a list of lines.
    `tool` is the EDA tool used to run the job.
    Returns the runtime, units as a tuple.
    Raises NotImplementedError exception if the EDA tool is not supported.
    """
    if tool == 'xcelium':
        return xcelium_job_runtime(log_text)
    elif tool == 'vcs':
        return vcs_job_runtime(log_text)
    else:
        raise NotImplementedError(f"{tool} is unsupported for job runtime "
                                  "extraction.")


def vcs_job_runtime(log_text: List) -> Tuple[float, str]:
    """Returns the VCS job runtime (wall clock time) along with its units.

    Search pattern example:
    CPU time: 22.170 seconds to compile + .518 seconds to elab + 1.901 \
        seconds to link
    CPU Time:      0.610 seconds;       Data structure size:   1.6Mb

    Returns the runtime, units as a tuple.
    Raises RuntimeError exception if the search pattern is not found.
    """
    pattern = r"^CPU [tT]ime:\s*(\d+\.?\d*?)\s*(seconds|minutes|hours).*$"
    for line in reversed(log_text):
        m = re.search(pattern, line)
        if m:
            return float(m.group(1)), m.group(2)[0]
    raise RuntimeError("Job runtime not found in the log.")


def xcelium_job_runtime(log_text: List) -> Tuple[float, str]:
    """Returns the Xcelium job runtime (wall clock time) along with its units.

    Search pattern example:
    TOOL:	xrun(64)	21.09-s006: Exiting on Aug 01, 2022 at 00:21:18 PDT \
        (total: 00:00:05)

    Returns the runtime, units as a tuple.
    Raises RuntimeError exception if the search pattern is not found.
    """
    pattern = (r"^TOOL:\s*xrun.*: Exiting on .*\(total:\s*(\d+):(\d+):(\d+)\)"
               r"\s*$")
    for line in reversed(log_text):
        m = re.search(pattern, line)
        if m:
            t = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3))
            return t, "s"
    raise RuntimeError("Job runtime not found in the log.")


def get_simulated_time(log_text: List, tool: str) -> Tuple[float, str]:
    """Returns the simulated time along with its units.

    EDA tools indicate how long the design was simulated for in the log file.
    This method invokes the tool specific method which parses the log text and
    returns the simulated time as a floating point value followed by its
    units (typically, pico|nano|micro|milliseconds) as a tuple.

    `log_text` is the job's log file contents as a list of lines.
    `tool` is the EDA tool used to run the job.
    Returns the simulated, units as a tuple.
    Raises NotImplementedError exception if the EDA tool is not supported.
    """
    if tool == 'xcelium':
        return xcelium_simulated_time(log_text)
    elif tool == 'vcs':
        return vcs_simulated_time(log_text)
    else:
        raise NotImplementedError(f"{tool} is unsupported for simulated time "
                                  "extraction.")


def xcelium_simulated_time(log_text: List) -> Tuple[float, str]:
    """Returns the Xcelium simulated time along with its units.

    Search pattern example:
    Simulation complete via $finish(2) at time 11724965 PS + 13

    Returns the simulated time, units as a tuple.
    Raises RuntimeError exception if the search pattern is not found.
    """
    pattern = r"^Simulation complete .* at time (\d+\.?\d*?)\s*(.?[sS]).*$"
    for line in reversed(log_text):
        m = re.search(pattern, line)
        if m:
            return float(m.group(1)), m.group(2).lower()
    raise RuntimeError("Simulated time not found in the log.")


def vcs_simulated_time(log_text: List) -> Tuple[float, str]:
    """Returns the VCS simulated time along with its units.

    Search pattern example:
               V C S   S i m u l a t i o n   R e p o r t
    Time: 12241752 ps

    Returns the simulated time, units as a tuple.
    Raises RuntimeError exception if the search pattern is not found.
    """
    pattern = r"^Time:\s*(\d+\.?\d*?)\s*(.?[sS])\s*$"
    next_line = ""
    for line in reversed(log_text):
        if "V C S   S i m u l a t i o n   R e p o r t" in line:
            m = re.search(pattern, next_line)
            if m:
                return float(m.group(1)), m.group(2).lower()
        next_line = line
    raise RuntimeError("Simulated time not found in the log.")
