#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Utility functions common across dvsim.
"""

import logging as log
import os
import pprint
import re
import shlex
import subprocess
import sys
import time
from collections import OrderedDict

import hjson
import mistletoe

# For verbose logging
VERBOSE = 15


# Run a command and get the result. Exit with error if the command did not
# succeed. This is a simpler version of the run_cmd function below.
def run_cmd(cmd):
    (status, output) = subprocess.getstatusoutput(cmd)
    if status:
        sys.stderr.write("cmd " + cmd + " returned with status " + str(status))
        sys.exit(status)
    return output


# Run a command with a specified timeout. If the command does not finish before
# the timeout, then it returns -1. Else it returns the command output. If the
# command fails, it throws an exception and returns the stderr.
def run_cmd_with_timeout(cmd, timeout=-1, exit_on_failure=1):
    args = shlex.split(cmd)
    p = subprocess.Popen(args,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)

    # If timeout is set, poll for the process to finish until timeout
    result = ""
    status = -1
    if timeout == -1:
        p.wait()
    else:
        start = time.time()
        while time.time() - start < timeout:
            if p.poll() is not None:
                break
            time.sleep(.01)

    # Capture output and status if cmd exited, else kill it
    if p.poll() is not None:
        result = p.communicate()[0]
        status = p.returncode
    else:
        log.error("cmd \"%s\" timed out!", cmd)
        p.kill()

    if status != 0:
        log.error("cmd \"%s\" exited with status %d", cmd, status)
        if exit_on_failure == 1: sys.exit(status)

    return (result, status)


# Parse hjson and return a dict
def parse_hjson(hjson_file):
    hjson_cfg_dict = None
    try:
        log.debug("Parsing %s", hjson_file)
        f = open(hjson_file, 'rU')
        text = f.read()
        hjson_cfg_dict = hjson.loads(text, use_decimal=True)
        f.close()
    except Exception as e:
        log.fatal(
            "Failed to parse \"%s\" possibly due to bad path or syntax error.\n%s",
            hjson_file, e)
        sys.exit(1)
    return hjson_cfg_dict


def subst_wildcards(var, mdict, ignored_wildcards=[], ignore_error=False):
    '''
    If var has wildcards specified within {..}, find and substitute them.
    '''
    def subst(wildcard, mdict):
        if wildcard in mdict.keys(): return mdict[wildcard]
        else: return None

    if "{eval_cmd}" in var:
        idx = var.find("{eval_cmd}") + 11
        subst_var = subst_wildcards(var[idx:], mdict, ignored_wildcards,
                                    ignore_error)
        # If var has wildcards that were ignored, then skip running the command
        # for now, assume that it will be handled later.
        match = re.findall(r"{([A-Za-z0-9\_]+)}", subst_var)
        if len(match) == 0:
            var = run_cmd(subst_var)
    else:
        match = re.findall(r"{([A-Za-z0-9\_]+)}", var)
        if len(match) > 0:
            subst_list = {}
            for item in match:
                if item not in ignored_wildcards:
                    log.debug("Found wildcard \"%s\" in \"%s\"", item, var)
                    found = subst(item, mdict)
                    if found is not None:
                        if type(found) is list:
                            subst_found = []
                            for element in found:
                                element = subst_wildcards(
                                    element, mdict, ignored_wildcards,
                                    ignore_error)
                                subst_found.append(element)
                            # Expand list into a str since list within list is
                            # not supported.
                            found = " ".join(subst_found)

                        elif type(found) is str:
                            found = subst_wildcards(found, mdict,
                                                    ignored_wildcards,
                                                    ignore_error)

                        elif type(found) is bool:
                            found = int(found)
                        subst_list[item] = found
                    else:
                        # Check if the wildcard exists as an environment variable
                        env_var = os.environ.get(item)
                        if env_var is not None: subst_list[item] = env_var
                        elif not ignore_error:
                            log.error(
                                "Substitution for the wildcard \"%s\" not found",
                                item)
                            sys.exit(1)
            for item in subst_list:
                var = var.replace("{" + item + "}", str(subst_list[item]))
    return var


def find_and_substitute_wildcards(sub_dict,
                                  full_dict,
                                  ignored_wildcards=[],
                                  ignore_error=False):
    '''
    Recursively find key values containing wildcards in sub_dict in full_dict
    and return resolved sub_dict.
    '''
    for key in sub_dict.keys():
        if type(sub_dict[key]) in [dict, OrderedDict]:
            # Recursively call this funciton in sub-dicts
            sub_dict[key] = find_and_substitute_wildcards(
                sub_dict[key], full_dict, ignored_wildcards, ignore_error)

        elif type(sub_dict[key]) is list:
            sub_dict_key_values = list(sub_dict[key])
            # Loop through the list of key's values and substitute each var
            # in case it contains a wildcard
            for i in range(len(sub_dict_key_values)):
                if type(sub_dict_key_values[i]) in [dict, OrderedDict]:
                    # Recursively call this funciton in sub-dicts
                    sub_dict_key_values[i] = \
                        find_and_substitute_wildcards(sub_dict_key_values[i],
                                                      full_dict, ignored_wildcards, ignore_error)

                elif type(sub_dict_key_values[i]) is str:
                    sub_dict_key_values[i] = subst_wildcards(
                        sub_dict_key_values[i], full_dict, ignored_wildcards,
                        ignore_error)

            # Set the substituted key values back
            sub_dict[key] = sub_dict_key_values

        elif type(sub_dict[key]) is str:
            sub_dict[key] = subst_wildcards(sub_dict[key], full_dict,
                                            ignored_wildcards, ignore_error)
    return sub_dict


def md_results_to_html(title, css_path, md_text):
    '''Convert results in md format to html. Add a little bit of styling.
    '''
    html_text = "<!DOCTYPE html>\n"
    html_text += "<html lang=\"en\">\n"
    html_text += "<head>\n"
    if title != "":
        html_text += "  <title>{}</title>\n".format(title)
    if css_path != "":
        html_text += "  <link rel=\"stylesheet\" type=\"text/css\""
        html_text += " href=\"{}\"/>\n".format(css_path)
    html_text += "</head>\n"
    html_text += "<body>\n"
    html_text += "<div class=\"results\">\n"
    html_text += mistletoe.markdown(md_text)
    html_text += "</div>\n"
    html_text += "</body>\n"
    html_text += "</html>\n"
    html_text = htmc_color_pc_cells(html_text)
    return html_text


def htmc_color_pc_cells(text):
    '''This function finds cells in a html table that contains a % sign. It then
    uses the number in front if the % sign to color the cell based on the value
    from a shade from red to green. These color styles are encoded in ./style.css
    which is assumed to be accessible by the final webpage.
    '''

    # Replace <td> with <td class="color-class"> based on the fp
    # value. "color-classes" are listed in ./style.css as follows: "cna"
    # for NA value, "c0" to "c10" for fp value falling between 0.00-9.99,
    # 10.00-19.99 ... 90.00-99.99, 100.0 respetively.
    def color_cell(cell, cclass):
        op = cell.replace("<td", "<td class=\"" + cclass + "\"")
        # Remove '%' sign.
        op = re.sub(r"\s*%\s*", "", op)
        return op

    # List of 'not applicable' identifiers.
    na_list = ['--', 'NA', 'N.A.', 'N.A', 'N/A', 'na', 'n.a.', 'n.a', 'n/a']
    na_list_patterns = '|'.join(na_list)

    # List of floating point patterns: '0', '0.0' & '.0'
    fp_patterns = "\d+|\d+\.\d+|\.\d+"

    patterns = fp_patterns + '|' + na_list_patterns
    match = re.findall(r"(<td.*>\s*(" + patterns + ")\s+%\s*</td>)", text)
    if len(match) > 0:
        subst_list = {}
        fp_nums = []
        for item in match:
            # item is a tuple - first is the full string indicating the table
            # cell which we want to replace, second is the floating point value.
            cell = item[0]
            fp_num = item[1]
            # Skip if fp_num is already processed.
            if fp_num in fp_nums: continue
            fp_nums.append(fp_num)
            if fp_num in na_list: subst = color_cell(cell, "cna")
            else:
                # Item is a fp num.
                try:
                    fp = float(fp_num)
                except ValueError:
                    log.error("Percentage item \"%s\" in cell \"%s\" is not an " + \
                              "integer or a floating point number", fp_num, cell)
                    continue
                if fp >= 0.0 and fp < 10.0: subst = color_cell(cell, "c0")
                elif fp >= 10.0 and fp < 20.0: subst = color_cell(cell, "c1")
                elif fp >= 20.0 and fp < 30.0: subst = color_cell(cell, "c2")
                elif fp >= 30.0 and fp < 40.0: subst = color_cell(cell, "c3")
                elif fp >= 40.0 and fp < 50.0: subst = color_cell(cell, "c4")
                elif fp >= 50.0 and fp < 60.0: subst = color_cell(cell, "c5")
                elif fp >= 60.0 and fp < 70.0: subst = color_cell(cell, "c6")
                elif fp >= 70.0 and fp < 80.0: subst = color_cell(cell, "c7")
                elif fp >= 80.0 and fp < 90.0: subst = color_cell(cell, "c8")
                elif fp >= 90.0 and fp < 100.0: subst = color_cell(cell, "c9")
                elif fp >= 100.0: subst = color_cell(cell, "c10")
            subst_list[cell] = subst
        for item in subst_list:
            text = text.replace(item, subst_list[item])
    return text
