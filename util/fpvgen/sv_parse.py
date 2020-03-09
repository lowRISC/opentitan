# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Helper functions for parsing a systemverilog module header.
"""

from io import StringIO
from pathlib import Path


class Param():
    name = ""
    datatype = ""
    style = ""
    value = ""

    def __init__(self, name_="", datatype_="", style_="", value_=""):
        self.name = name_
        self.datatype = datatype_
        self.style = style_
        self.value = value_


class Port():
    name = ""
    datatype = ""
    direction = ""

    def __init__(self, name_="", datatype_="", direction_=""):
        self.name = name_
        self.datatype = datatype_
        self.direction = direction_


class Dut():
    name = ""
    pkgs = []
    params = []
    ports = []
    deps = []
    is_cip = False

    def __init__(self, name_="", pkgs_=[], ports_=[], \
        params_=[], deps_=[], is_cip_=False):
        self.name = name_
        self.pkgs = pkgs_
        self.ports = ports_
        self.params = params_
        self.deps = deps_
        self.is_cip = is_cip_

    # filters out localparams
    def get_param_style(self, style):
      params = []
      for p in self.params:
        params += [p] if p.style == style else []
      return params

# strip // comments
def strip_comments(buf):
    outbuf = ""
    for line in buf.split('\n'):
        for k in range(len(line) - 1):
            if line[k:k + 2] == "//":
                break
            else:
                outbuf += line[k]
        else:
            if line:
                outbuf += line[-1]
        outbuf += " "

    return outbuf


PARENTH_STYLES = {'(': ')', '[': ']', '{': '}'}


# parse parenthesis and optionally handle the body using the handler function
# if no handler is specified, it just calls itself recursively
def parse_parenthesis(hdl_raw, dut, style='(', handler=None):
    if style not in PARENTH_STYLES:
        print("Unknown parenthesis style %s, aborting." % style)
    else:
        par_opened = False
        while hdl_raw:
            c = hdl_raw.pop(0)
            if c == style:
                par_opened = True
                if handler:
                    handler(hdl_raw, dut)
                else:
                    parse_parenthesis(hdl_raw, dut, style)
            if c == PARENTH_STYLES[style]:
                if not par_opened:
                    hdl_raw.insert(0, c)
                break
    return


# parse individual port declarations
# may not be fully correct with unpacked dimensions,
# but works for the common case
def parse_port(buf, dut):
    words = buf.split()
    if words:
        if words[0] not in ["input", "inout", "output"]:
            print("Warning, expected input, inout or output keyword")
        else:
            if len(words) > 2:
                dut.ports += [Port(words[-1], "".join(words[1:-1]), words[0])]
            elif len(words) == 2:
                dut.ports += [Port(words[-1], "", words[0])]
            else:
                print("Warning, port declaration incomplete")
    else:
        print("Warning, port declaration empty")
    return


# parse individual parameter declaration
def parse_param(buf, dut):
    words = buf.split('=')
    value = '='.join(words[1:])
    words = words[0].split()

    if words:
        if words[0] not in ["parameter", "localparam"]:
            print("Warning, expected parameter or localparam keyword")
        else:
            if len(words) > 2:
                dut.params += [
                    Param(words[-1], " ".join(words[1:-1]), words[0], value)
                ]
            elif len(words) == 2:
                dut.params += [Param(words[-1], "", words[0], value)]
            else:
                print("Warning, parameter declaration incomplete")
    else:
        print("Warning, port declaration empty")
    return


# extract individual declarations
def parse_declaration(hdl_raw, dut, handler):
    buf = ""
    par_opened = 0
    while hdl_raw:
        c = hdl_raw.pop(0)
        # end of this port
        if c == ',':
            handler(buf, dut)
            buf = ""
        elif c == '(':
            par_opened = par_opened + 1
            buf += c
        elif c == ')':
            if par_opened:
                # part of the declaration
                par_opened = par_opened - 1
                buf += c
            else:
                # end of the declaration list
                handler(buf, dut)
                hdl_raw.insert(0, ')')
                break
        else:
            buf += c
    return


def parse_ports(hdl_raw, dut):
    parse_declaration(hdl_raw, dut, parse_port)


def parse_params(hdl_raw, dut):
    parse_declaration(hdl_raw, dut, parse_param)


def parse_module(words, dut):
    # check for imports first
    while words:
        w = words.pop(0)
        if w == "import":
            if words:
                # get package names to import
                pkg = words.pop(0).split(";")
                dut.pkgs += [pkg[0]]
            else:
                print("Unexpected end")
        # stop package scan and move on to body
        elif '#' in w or '(' in w:
            words.insert(0, w)
            break

    hdl_raw = list(' '.join(words))
    while hdl_raw:
        c = hdl_raw.pop(0)
        if c == '#':
            parse_parenthesis(hdl_raw, dut, '(', parse_params)
        elif c == '(':
            hdl_raw.insert(0, '(')
            parse_parenthesis(hdl_raw, dut, '(', parse_ports)
        elif c == ';':
            break
    return


# simplistic module declaration parser.
# this works in most cases, but there are exceptions.
def parse_file(file):
    dut = Dut()
    hdl_raw = ""
    with open(file, 'r') as fp:
        hdl_raw = strip_comments(fp.read())
    # extract first module declaration in file and extract port list
    # also look for imported packages (either in the module declaration
    # or before it)
    words = hdl_raw.split()
    while words:
        w = words.pop(0)
        if w == "import":
            if words:
                # get package names to import
                pkg = words.pop(0).split(";")
                dut.pkgs += [pkg[0]]
            else:
                print("Unexpected end")
        elif w == "module":
            if words:
                # get module name
                dut.name = words[0]
                # parse the module params and port list and exit
                parse_module(words, dut)
            break
    return dut
