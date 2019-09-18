# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate SystemVerilog designs from validated register json tree
"""

import logging as log
import operator
import sys

from mako.template import Template
from pkg_resources import resource_filename

from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess


class Field():
    """Field in a register.

    Field class contains necessary info to generate RTL code.
    It has two additional (tool generated) feidls, swrdaccess and swwraccess,
    which represent read and write type. This makes RTL generation code simpler.
    """
    name = ""  # required
    msb = 31  # required
    lsb = 0  # required
    resval = 0  # optional
    swaccess = SwAccess.NONE  # optional
    swrdaccess = SwRdAccess.NONE
    swwraccess = SwWrAccess.NONE
    hwaccess = HwAccess.HRO
    hwqe = False
    hwre = False

    def __init__(self):
        self.name = ""  # required
        self.msb = 31  # required
        self.lsb = 0  # required
        self.resval = 0  # optional
        self.swaccess = SwAccess.NONE  # optional
        self.swrdaccess = SwRdAccess.NONE
        self.swwraccess = SwWrAccess.NONE
        self.hwaccess = HwAccess.HRO
        self.hwqe = False
        self.hwre = False


class Register():
    name = ""
    offset = 0
    hwqe = False
    hwre = False
    hwext = False  # External register
    resval = 0
    dvrights = "RO"  # Used by UVM REG only
    regwen = ""
    fields = []
    width = 0  # indicate register size

    def __init__(self):
        self.name = ""
        self.offset = 0
        self.hwqe = False
        self.hwre = False
        self.hwext = False  # External register
        self.resval = 0
        self.dvrights = "RO"  # Used by UVM REG only
        self.regwen = ""
        self.fields = []
        self.width = 0


class Window():
    base_addr = 0
    limit_addr = 0
    n_bits = 0

    def __init__(self):
        self.base_addr = 0
        self.limit_addr = 0
        self.n_bits = 0


class Block():
    width = 32
    addr_width = 12
    base_addr = 0
    name = ""
    regs = []
    wins = []
    blocks = []

    def __init__(self):
        self.width = 32
        self.addr_width = 12
        self.base_addr = 0
        self.name = ""
        self.regs = []
        self.wins = []
        self.blocks = []


def escape_name(name):
    return name.lower().replace(' ', '_')


def check_field_bool(obj, field, default):
    if field in obj:
        return True if obj[field] == "true" else False
    else:
        return default


def parse_field(obj, reg, nfields):
    """Convert OrderedDict field into Field class
    """
    f = Field()
    f.name = escape_name(obj["name"])
    # if name doesn't exist and only one field in a reg
    if f.name == "" and nfields == 1:
        f.name = reg.name

    # MSB, LSB
    f.lsb = obj["bitinfo"][2]
    f.msb = f.lsb + obj["bitinfo"][1] - 1

    #assert not 'swaccess' in obj, "R[%s] F[%s]: SwAccess in Field not supported" % (reg.name, f.name)
    f.swaccess = obj["genswaccess"]
    f.swrdaccess = obj["genswrdaccess"]
    f.swwraccess = obj["genswwraccess"]
    f.hwaccess = obj["genhwaccess"]
    f.hwqe = obj["genhwqe"]
    f.hwre = obj["genhwre"]

    # resval handling. `genresval` has zero value if `resval` field is defined
    # as unknown 'x'
    f.resval = obj["genresval"]

    return f


def parse_reg(obj):
    """Convert OrderedDict register into Register class
    """

    reg = Register()
    reg.name = escape_name(obj['name'])
    reg.offset = obj["genoffset"]
    reg.fields = []

    reg.hwext = (obj['hwext'] == "true")
    reg.hwqe = (obj["hwqe"] == "true")
    reg.hwre = (obj["hwre"] == "true")
    reg.resval = obj["genresval"]
    reg.dvrights = obj["gendvrights"]
    reg.regwen = obj["regwen"].lower()

    # Parsing Fields
    for f in obj["fields"]:
        field = parse_field(f, reg, len(obj["fields"]))
        if field != None:
            reg.fields.append(field)
            reg.width = max(reg.width, field.msb + 1)

    # TODO(eunchan): Field bitfield overlapping check
    log.info("R[0x%04x]: %s ", reg.offset, reg.name)
    for f in reg.fields:
        log.info("  F[%2d:%2d]: %s", f.msb, f.lsb, f.name)

    return reg


def parse_win(obj, width):
    # Convert register window fields into Window class
    # base_addr : genoffset
    # limit_addr : genoffset + items*width
    win = Window()
    win.name = obj["name"]
    win.base_addr = obj["genoffset"]
    win.limit_addr = obj["genoffset"] + int(obj["items"]) * (width // 8)
    win.dvrights = obj["swaccess"]
    win.n_bits = obj["genvalidbits"]

    # TODO: Generate warnings of `noalign` or `unusual`
    return win


def json_to_reg(obj):
    """Converts json OrderedDict into structure having useful information for
    Template to use.

    Main purpose of this function is:
        - Add Offset value based on auto calculation
        - Prepare Systemverilog data structure to generate _pkg file
    """
    block = Block()

    # Name
    block.name = escape_name(obj["name"])
    log.info("Processing module: %s", block.name)

    block.width = int(obj["regwidth"], 0)

    if block.width != 32 and block.width != 64:
        log.error(
            "Current reggen tool doesn't support field width that is not 32 nor 64"
        )

    log.info("Data Width is set to %d bits", block.width)

    for r in obj["registers"]:
        # Check if any exception condition hit
        if 'reserved' in r:
            continue
        elif 'skipto' in r:
            continue
        elif 'sameaddr' in r:
            log.error("Current tool doesn't support 'sameaddr' type")
            continue
        elif 'window' in r:
            win = parse_win(r['window'], block.width)
            if win != None:
                block.wins.append(win)
            continue
        elif 'multireg' in r:
            for genr in r['multireg']['genregs']:
                reg = parse_reg(genr)
                if reg != None:
                    block.regs.append(reg)
            continue
        reg = parse_reg(r)
        if reg != None:
            block.regs.append(reg)
        # mdhayter -- moved logging into parse_regs

    # Last offset and calculate space
    #  Later on, it could use block.regs[-1].genoffset
    if "space" in obj:
        block.addr_width = int(obj["space"], 0).bit_length()
    else:
        block.addr_width = (obj["gensize"] - 1).bit_length()

    return block


def gen_rtl(obj, outdir):
    # obj: OrderedDict

    block = json_to_reg(obj)

    # Read Register templates
    reg_top_tpl = Template(
        filename=resource_filename('reggen', 'reg_top.tpl.sv'))
    reg_pkg_tpl = Template(
        filename=resource_filename('reggen', 'reg_pkg.tpl.sv'))

    # Generate pkg.sv with block name
    with open(outdir + "/" + block.name + "_reg_pkg.sv", 'w',
              encoding='UTF-8') as fout:
        fout.write(
            reg_pkg_tpl.render(block=block,
                               HwAccess=HwAccess,
                               SwRdAccess=SwRdAccess,
                               SwWrAccess=SwWrAccess))

    # Generate top.sv
    with open(outdir + "/" + block.name + "_reg_top.sv", 'w',
              encoding='UTF-8') as fout:
        fout.write(
            reg_top_tpl.render(block=block,
                               HwAccess=HwAccess,
                               SwRdAccess=SwRdAccess,
                               SwWrAccess=SwWrAccess))
