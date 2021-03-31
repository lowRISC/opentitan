# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Utility functions common across dvsim.
"""

import logging as log
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from collections import OrderedDict
from datetime import datetime
from pathlib import Path

import hjson
import mistletoe
from premailer import transform

# For verbose logging
VERBOSE = 15

# Timestamp format when creating directory backups.
TS_FORMAT = "%y.%m.%d_%H.%M.%S"

# Timestamp format when generating reports.
TS_FORMAT_LONG = "%A %B %d %Y %H:%M:%S UTC"


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
        if exit_on_failure == 1:
            sys.exit(status)

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


def _stringify_wildcard_value(value):
    '''Make sense of a wildcard value as a string (see subst_wildcards)

    Strings are passed through unchanged. Integer or boolean values are printed
    as numerical strings. Lists or other sequences have their items printed
    separated by spaces.

    '''
    if type(value) is str:
        return value

    if type(value) in [bool, int]:
        return str(int(value))

    try:
        return ' '.join(_stringify_wildcard_value(x) for x in value)
    except TypeError:
        raise ValueError('Wildcard had value {!r} which is not of a supported '
                         'type.'.format(value))


def _subst_wildcards(var, mdict, ignored, ignore_error, seen):
    '''Worker function for subst_wildcards

    seen is a list of wildcards that have been expanded on the way to this call
    (used for spotting circular recursion).

    Returns (expanded, seen_err) where expanded is the new value of the string
    and seen_err is true if we stopped early because of an ignored error.

    '''
    wildcard_re = re.compile(r"{([A-Za-z0-9\_]+)}")

    # Work from left to right, expanding each wildcard we find. idx is where we
    # should start searching (so that we don't keep finding a wildcard that
    # we've decided to ignore).
    idx = 0

    any_err = False

    while True:
        right_str = var[idx:]
        match = wildcard_re.search(right_str)

        # If no match, we're done.
        if match is None:
            return (var, any_err)

        name = match.group(1)

        # If the name should be ignored, skip over it.
        if name in ignored:
            idx += match.end()
            continue

        # If the name has been seen already, we've spotted circular recursion.
        # That's not allowed!
        if name in seen:
            raise ValueError('String contains circular expansion of '
                             'wildcard {!r}.'.format(match.group(0)))

        # Treat eval_cmd specially
        if name == 'eval_cmd':
            cmd = _subst_wildcards(right_str[match.end():], mdict, ignored,
                                   ignore_error, seen)[0]

            # Are there any wildcards left in cmd? If not, we can run the
            # command and we're done.
            cmd_matches = list(wildcard_re.finditer(cmd))
            if not cmd_matches:
                var = var[:match.start()] + run_cmd(cmd)
                continue

            # Otherwise, check that each of them is ignored, or that
            # ignore_error is True.
            bad_names = False
            if not ignore_error:
                for cmd_match in cmd_matches:
                    if cmd_match.group(1) not in ignored:
                        bad_names = True

            if bad_names:
                raise ValueError('Cannot run eval_cmd because the command '
                                 'expands to {!r}, which still contains a '
                                 'wildcard.'.format(cmd))

            # We can't run the command (because it still has wildcards), but we
            # don't want to report an error either because ignore_error is true
            # or because each wildcard that's left is ignored. Return the
            # partially evaluated version.
            return (var[:idx] + right_str[:match.end()] + cmd, True)

        # Otherwise, look up name in mdict.
        value = mdict.get(name)

        # If the value isn't set, check the environment
        if value is None:
            value = os.environ.get(name)

        if value is None:
            # Ignore missing values if ignore_error is True.
            if ignore_error:
                idx += match.end()
                continue

            raise ValueError('String to be expanded contains '
                             'unknown wildcard, {!r}.'.format(match.group(0)))

        value = _stringify_wildcard_value(value)

        # Do any recursive expansion of value, adding name to seen (to avoid
        # circular recursion).
        value, saw_err = _subst_wildcards(value, mdict, ignored, ignore_error,
                                          seen + [name])

        # Replace the original match with the result and go around again. If
        # saw_err, increment idx past what we just inserted.
        var = (var[:idx] + right_str[:match.start()] + value +
               right_str[match.end():])
        if saw_err:
            any_err = True
            idx += match.start() + len(value)


def subst_wildcards(var, mdict, ignored_wildcards=[], ignore_error=False):
    '''Substitute any "wildcard" variables in the string var.

    var is the string to be substituted. mdict is a dictionary mapping
    variables to strings. ignored_wildcards is a list of wildcards that
    shouldn't be substituted. ignore_error means to partially evaluate rather
    than exit on an error.

    A wildcard is written as a name (alphanumeric, allowing backslash and
    underscores) surrounded by braces. For example,

      subst_wildcards('foo {x} baz', {'x': 'bar'})

    returns "foo bar baz". Dictionary values can be strings, booleans, integers
    or lists. For example:

      subst_wildcards('{a}, {b}, {c}, {d}',
                      {'a': 'a', 'b': True, 'c': 42, 'd': ['a', 10]})

    returns 'a, 1, 42, a 10'.

    If a wildcard is in ignored_wildcards, it is ignored. For example,

      subst_wildcards('{a} {b}', {'b': 'bee'}, ignored_wildcards=['a'])

    returns "{a} bee".

    If a wildcard appears in var but is not in mdict, the environment is
    checked for the variable. If the name still isn't found, the default
    behaviour is to log an error and exit. If ignore_error is True, the
    wildcard is ignored (as if it appeared in ignore_wildcards).

    If {eval_cmd} appears in the string and 'eval_cmd' is not in
    ignored_wildcards then the following text is recursively expanded. The
    result of this expansion is treated as a command to run and the text is
    replaced by the output of the command.

    If a wildcard has been ignored (either because of ignored_wildcards or
    ignore_error), the command to run in eval_cmd might contain a match for
    wildcard_re. If ignore_error is True, the command is not run. So

       subst_wildcards('{eval_cmd}{foo}', {}, ignore_error=True)

    will return '{eval_cmd}{foo}' unchanged. If ignore_error is False, the
    function logs an error and exits.

    Recursion is possible in subst_wildcards. For example,

      subst_wildcards('{a}', {'a': '{b}', 'b': 'c'})

    returns 'c'. Circular recursion is detected, however. So

      subst_wildcards('{a}', {'a': '{b}', 'b': '{a}'})

    will log an error and exit. This error is raised whether or not
    ignore_error is set.

    Since subst_wildcards works from left to right, it's possible to compute
    wildcard names with code like this:

      subst_wildcards('{a}b}', {'a': 'a {', 'b': 'bee'})

    which returns 'a bee'. This is pretty hard to read though, so is probably
    not a good idea to use.

    '''
    try:
        return _subst_wildcards(var, mdict, ignored_wildcards, ignore_error,
                                [])[0]
    except ValueError as err:
        log.error(str(err))
        sys.exit(1)


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


def md_results_to_html(title, css_file, md_text):
    '''Convert results in md format to html. Add a little bit of styling.
    '''
    html_text = "<!DOCTYPE html>\n"
    html_text += "<html lang=\"en\">\n"
    html_text += "<head>\n"
    if title != "":
        html_text += "  <title>{}</title>\n".format(title)
    html_text += "</head>\n"
    html_text += "<body>\n"
    html_text += "<div class=\"results\">\n"
    html_text += mistletoe.markdown(md_text)
    html_text += "</div>\n"
    html_text += "</body>\n"
    html_text += "</html>\n"
    html_text = htmc_color_pc_cells(html_text)
    # this function converts css style to inline html style
    html_text = transform(html_text,
                          external_styles=css_file,
                          cssutils_logging_level=log.ERROR)
    return html_text


def htmc_color_pc_cells(text):
    '''This function finds cells in a html table that contain numerical values
    (and a few known strings) followed by a single space and an identifier.
    Depending on the identifier, it shades the cell in a specific way. A set of
    12 color palettes for setting those shades are encoded in ./style.css.
    These are 'cna' (grey), 'c0' (red), 'c1' ... 'c10' (green). The shade 'cna'
    is used for items that are maked as 'not applicable'. The shades 'c1' to
    'c9' form a gradient from red to lime-green to indicate 'levels of
    completeness'. 'cna' is used for greying out a box for 'not applicable'
    items, 'c0' is for items that are considered risky (or not yet started) and
    'c10' for items that have completed successfully, or that are
    'in good standing'.

    These are the supported identifiers: %, %u, G, B, E, W, EN, WN.
    The shading behavior for these is described below.

    %:  Coloured percentage, where the number in front of the '%' sign is mapped
        to a color for the cell ranging from red ('c0') to green ('c10').
    %u: Uncoloured percentage, where no markup is applied and '%u' is replaced
        with '%' in the output.
    G:  This stands for 'Good' and results in a green cell.
    B:  This stands for 'Bad' and results in a red cell.
    E:  This stands for 'Errors' and the cell is colored with red if the number
        in front of the indicator is larger than 0. Otherwise the cell is
        colored with green.
    W:  This stands for 'Warnings' and the cell is colored with yellow ('c6')
        if the number in front of the indicator is larger than 0. Otherwise
        the cell is colored with green.
    EN: This stands for 'Errors Negative', which behaves the same as 'E' except
        that the cell is colored red if the number in front of the indicator is
        negative.
    WN: This stands for 'Warnings Negative', which behaves the same as 'W'
        except that the cell is colored yellow if the number in front of the
        indicator is negative.

    N/A items can have any of the following indicators and need not be
    preceeded with a numerical value:

    '--', 'NA', 'N.A.', 'N.A', 'N/A', 'na', 'n.a.', 'n.a', 'n/a'

    '''

    # Replace <td> with <td class="color-class"> based on the fp
    # value. "color-classes" are listed in ./style.css as follows: "cna"
    # for NA value, "c0" to "c10" for fp value falling between 0.00-9.99,
    # 10.00-19.99 ... 90.00-99.99, 100.0 respetively.
    def color_cell(cell, cclass, indicator="%"):
        op = cell.replace("<td", "<td class=\"" + cclass + "\"")
        # Remove the indicator.
        op = re.sub(r"\s*" + indicator + r"\s*", "", op)
        return op

    # List of 'not applicable' identifiers.
    na_list = ['--', 'NA', 'N.A.', 'N.A', 'N/A', 'na', 'n.a.', 'n.a', 'n/a']
    na_list_patterns = '|'.join(na_list)

    # List of floating point patterns: '0', '0.0' & '.0'
    fp_patterns = r"[\+\-]?\d+\.?\d*"

    patterns = fp_patterns + '|' + na_list_patterns
    indicators = "%|%u|G|B|E|W|EN|WN"
    match = re.findall(
        r"(<td.*>\s*(" + patterns + r")\s+(" + indicators + r")\s*</td>)",
        text)
    if len(match) > 0:
        subst_list = {}
        fp_nums = []
        for item in match:
            # item is a tuple - first is the full string indicating the table
            # cell which we want to replace, second is the floating point value.
            cell = item[0]
            fp_num = item[1]
            indicator = item[2]
            # Skip if fp_num is already processed.
            if (fp_num, indicator) in fp_nums:
                continue
            fp_nums.append((fp_num, indicator))
            if fp_num in na_list:
                subst = color_cell(cell, "cna", indicator)
            else:
                # Item is a fp num.
                try:
                    fp = float(fp_num)
                except ValueError:
                    log.error(
                        "Percentage item \"%s\" in cell \"%s\" is not an "
                        "integer or a floating point number", fp_num, cell)
                    continue
                # Percentage, colored.
                if indicator == "%":
                    if fp >= 0.0 and fp < 10.0:
                        subst = color_cell(cell, "c0")
                    elif fp >= 10.0 and fp < 20.0:
                        subst = color_cell(cell, "c1")
                    elif fp >= 20.0 and fp < 30.0:
                        subst = color_cell(cell, "c2")
                    elif fp >= 30.0 and fp < 40.0:
                        subst = color_cell(cell, "c3")
                    elif fp >= 40.0 and fp < 50.0:
                        subst = color_cell(cell, "c4")
                    elif fp >= 50.0 and fp < 60.0:
                        subst = color_cell(cell, "c5")
                    elif fp >= 60.0 and fp < 70.0:
                        subst = color_cell(cell, "c6")
                    elif fp >= 70.0 and fp < 80.0:
                        subst = color_cell(cell, "c7")
                    elif fp >= 80.0 and fp < 90.0:
                        subst = color_cell(cell, "c8")
                    elif fp >= 90.0 and fp < 100.0:
                        subst = color_cell(cell, "c9")
                    elif fp >= 100.0:
                        subst = color_cell(cell, "c10")
                # Percentage, uncolored.
                elif indicator == "%u":
                    subst = cell.replace("%u", "%")
                # Good: green
                elif indicator == "G":
                    subst = color_cell(cell, "c10", indicator)
                # Bad: red
                elif indicator == "B":
                    subst = color_cell(cell, "c0", indicator)
                # Bad if positive: red for errors, yellow for warnings,
                # otherwise green.
                elif indicator in ["E", "W"]:
                    if fp <= 0:
                        subst = color_cell(cell, "c10", indicator)
                    elif indicator == "W":
                        subst = color_cell(cell, "c6", indicator)
                    elif indicator == "E":
                        subst = color_cell(cell, "c0", indicator)
                # Bad if negative: red for errors, yellow for warnings,
                # otherwise green.
                elif indicator in ["EN", "WN"]:
                    if fp >= 0:
                        subst = color_cell(cell, "c10", indicator)
                    elif indicator == "WN":
                        subst = color_cell(cell, "c6", indicator)
                    elif indicator == "EN":
                        subst = color_cell(cell, "c0", indicator)
            subst_list[cell] = subst
        for item in subst_list:
            text = text.replace(item, subst_list[item])
    return text


def print_msg_list(msg_list_title, msg_list, max_msg_count=-1):
    '''This function prints a list of messages to Markdown.

    The argument msg_list_title contains a string for the list title, whereas
    the msg_list argument contains the actual list of message strings.
    max_msg_count limits the number of messages to be printed (set to negative
    number to print all messages).

    Example:

    print_msg_list("### Tool Warnings", ["Message A", "Message B"], 10)
    '''
    md_results = ""
    if msg_list:
        md_results += msg_list_title + "\n"
        md_results += "```\n"
        for k, msg in enumerate(msg_list):
            if k <= max_msg_count or max_msg_count < 0:
                md_results += msg + "\n\n"
            else:
                md_results += "Note: %d more messages have been suppressed " % (
                    len(msg_list) - max_msg_count)
                md_results += "(max_msg_count = %d) \n\n" % (max_msg_count)
                break
        md_results += "```\n"
    return md_results


def rm_path(path, ignore_error=False):
    '''Removes the specified path if it exists.

    'path' is a Path-like object. If it does not exist, the function simply
    returns. If 'ignore_error' is set, then exception caught by the remove
    operation is raised, else it is ignored.
    '''

    exc = None
    try:
        os.remove(path)
    except FileNotFoundError:
        pass
    except IsADirectoryError:
        try:
            shutil.rmtree(path)
        except OSError as e:
            exc = e
    except OSError as e:
        exc = e

    if exc:
        log.error("Failed to remove {}:\n{}.".format(path, exc))
        if not ignore_error:
            raise exc


def clean_odirs(odir, max_odirs, ts_format=TS_FORMAT):
    """Clean previous output directories.

    When running jobs, we may want to maintain a limited history of
    previous invocations. This method finds and deletes the output
    directories at the base of input arg 'odir' with the oldest timestamps,
    if that limit is reached. It returns a list of directories that
    remain after deletion.
    """

    if os.path.exists(odir):
        # If output directory exists, back it up.
        ts = datetime.fromtimestamp(os.stat(odir).st_ctime).strftime(ts_format)
        shutil.move(odir, "{}_{}".format(odir, ts))

    # Get list of past output directories sorted by creation time.
    pdir = Path(odir).resolve().parent
    if not pdir.exists():
        return []

    dirs = sorted([old for old in pdir.iterdir() if old.is_dir()],
                  key=os.path.getctime,
                  reverse=True)

    for old in dirs[max(0, max_odirs - 1):]:
        shutil.rmtree(old, ignore_errors=True)

    return [] if max_odirs == 0 else dirs[:max_odirs - 1]
