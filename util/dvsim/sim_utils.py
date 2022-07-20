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

    EDA tools indicate how long the job ran in terms of CPU time in the log file.
    This method invokes the tool specific method which parses the log text and
    returns the runtime as a floating point value followed by its units as a tuple.

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
        raise NotImplementedError(f"{tool} is unsupported for job runtime extraction.")


def vcs_job_runtime(log_text: List) -> Tuple[float, str]:
    """Capture and return the job_runtime along with its units from VCS simulator.

    Example of VCS job_runtime: 'CPU Time:      1.210 seconds;'
    Raises SyntaxError exception if we find the specific line but fail to parse the
    actual number with unit.
    """
    # Reverse the log_text because the runtime is usually printed at the end of
    # the file.
    for line in reversed(log_text):
        if "CPU Time" in line:
            # Find pattern: CPU Time: "XXXX" seconds;.
            m = re.search(r"(\d+\.\d+)", line)
            if m:
                return float(m.group(0)), "s"
            else:
                raise SyntaxError("Cannot find job runtime in line: " + line)
    # We cannot find the job runtime summary line, could due to job killed,
    # return the default value.
    return 0, "s"


def xcelium_job_runtime(log_text: List) -> Tuple[float, str]:
    """Capture and return the job_runtime along with its units from Xcelium simulator.

    Example of Xcelium job_runtime:
      'TOOL: xrun(64) 21.09-s006: Exiting on Jul 22, 2022 at 13:38:48 PDT (total: 00:00:02)'
    Raises SyntaxError exception if we find the specific line but fail to parse the
    actual number with unit.
    """
    # Reverse the log_text because the runtime is usually printed at the end of
    # the file.
    for line in reversed(log_text):
        if "total:" in line and "TOOL" in line:
            # Find pattern: TOOL .. (total: "XX":"XX":"XX")
            m = re.search(r"total:.*(\d+):(\d+):(\d+)", line)
            if m:
                # Convert time format: HR:MIN:SEC to seconds.
                val = re.findall(r"\d+", m.group(0))
                job_runtime = (int(val[0]) * 60 + int(val[1])) * 60 + int(val[2])
                return job_runtime, "s"
            else:
                raise SyntaxError("Cannot find job runtime in line: " + line)
    # We cannot find the job runtime summary line, could due to job killed,
    # return the default value.
    return 0, "s"


def get_simulated_time(log_text: List, tool: str) -> Tuple[float, str]:
    """Returns the job simulated time along with its units.
    This method invokes the tool specific method which parses the log text and
    returns the simulated time as a floating point value followed by its units as a tuple.
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
        raise NotImplementedError("{tool} is unsupported for run times extraction.")


def xcelium_simulated_time(log_text: List) -> Tuple[float, str]:
    """Capture and return the simulated_time along with its units from Xcelium simulator.

    Example of Xcelium simulated_time:
      'Simulation complete via $finish(2) at time 43361308 PS + 58'
    Raises SyntaxError exception if we find the specific line but fail to parse the
    actual number with unit.
    """

    # Reverse the log_text because Xcelium does not print out the total
    # simulation time in summary, so we parse the log in reversed order to get
    # the last simulation timestamp.
    for line in reversed(log_text):
        if "Simulation complete via" in line:
            m = re.search(r"at time.*(\b\d+).+(\b[A-Z]+)", line)
            if m:
                return int(m.group(1)), m.group(2).lower()
            else:
                raise SyntaxError("Cannot find the simulation time in line: " + line)
    # We cannot find the job simulated time summary line, could due to job killed,
    # return the default value.
    return 0, "s"


def vcs_simulated_time(log_text: List) -> Tuple[float, str]:
    """Capture and return the simulated_time along with its units from VCS simulator.

    Example of VCS simulated_time: '$finish at simulation time 522104678 ps'
    Raises SyntaxError exception if we find the specific line but fail to parse the
    actual number with unit.
    """

    # Reverse the log_text because the simulation time is usually printed at the end of
    # the file.
    for line in reversed(log_text):
        if "finish at simulation time" in line:
            m = re.search(r"(\d+).+(\b[a-z]+)", line)
            if m:
                return int(m.group(1)), m.group(2)
            else:
                raise SyntaxError("Cannot find the simulation time in line: " + line)
    # We cannot find the job simulated time summary line, could due to job killed,
    # return the default value.
    return 0, "s"
