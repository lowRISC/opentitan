# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Register JSON validation
"""

import logging as log
import sys

from reggen.field_enums import *


# Routine that can be used for Hjson object_pairs_hook
# The baseline is dict(pairs) i.e. construct a dictonary from pairs
# The usual is OrderedDict(pairs) which is redundant in latest python
# Both of these silently allow repeated keys, which this version detects
def checking_dict(pairs):
    d = {}
    for x in pairs:
        if x[0] in d:
            repkey = 'Repeated' + x[0]
            log.warn("Repeated key " + x[0] + " added as " + repkey)
            d[repkey] = x[1]
        else:
            d[x[0]] = x[1]
    return d


def check_count(top, mreg, err_prefix):
    '''Checking mreg count if it is in param list
    '''
    if not "param_list" in top:
        top["param_list"] = []
        name_list = []
    else:
        name_list = [z["name"] for z in top["param_list"]]

    try:
        index = name_list.index(mreg["count"])
        return check_int(top["param_list"][index]["default"],
                         err_prefix + " default")
    except ValueError:
        # cannot find entry in the param list
        log.warning(err_prefix + " is integer. " +
                    "It is recommended to use Parameter.")
        mcount, ierr = check_int(mreg["count"], err_prefix)
        if ierr != 0:
            return mcount, ierr

        top["param_list"].append({
            "name": mreg["name"],
            "type": "int",
            "default": mcount,
            "desc": "auto added parameter",
            "local": "true"
        })
        log.info("Parameter {} is added".format(mreg["name"]))
        # Replace count integer to parameter
        mreg["count"] = mreg["name"]

        return mcount, ierr


# validating version of int(x, 0)
# returns int value, error flag
# if error flag is True value will be zero
def check_int(x, err_prefix):
    if isinstance(x, int):
        return x, False
    if x[0] == '0' and len(x) > 2:
        if x[1] in 'bB':
            validch = '01'
        elif x[1] in 'oO':
            validch = '01234567'
        elif x[1] in 'xX':
            validch = '0123456789abcdefABCDEF'
        else:
            log.error(err_prefix +
                      ": int must start digit, 0b, 0B, 0o, 0O, 0x or 0X")
            return 0, True
        for c in x[2:]:
            if not c in validch:
                log.error(err_prefix + ": Bad character " + c + " in " + x)
                return 0, True
    else:
        if not x.isdecimal():
            log.error(err_prefix + ": Number not valid int " + x)
            return 0, 1
    return int(x, 0), False


def check_bool(x, err_prefix):
    """check_bool checks if input 'x' is one of the list:
        "true", "false"

        It returns value as Bool type and Error condition.
    """
    if isinstance(x, bool):
        # if Bool returns as it is
        return x, False
    if not x.lower() in ["true", "false"]:
        log.error(err_prefix + ": Bad field value " + x)
        return False, True
    else:
        return (x.lower() == "true"), False


def check_ln(obj, x, withwidth, err_prefix):
    error = 0
    if not isinstance(obj[x], list):
        log.error(err_prefix + ' element ' + x + ' not a list')
        return 1
    for y in obj[x]:
        error += check_keys(y, ln_required, ln_optional if withwidth else {},
                            {}, err_prefix + ' element ' + x)
        if withwidth:
            if 'width' in y:
                w, err = check_int(y['width'], err_prefix + ' width in ' + x)
                if err:
                    error += 1
                    w = 1
            else:
                w = 1
            y['width'] = str(w)

    return error


def check_lp(obj, x, err_prefix):
    error = 0
    if not isinstance(obj[x], list):
        log.error(err_prefix + ' element ' + x + ' not a list')
        return 1

    for y in obj[x]:
        error += check_keys(y, lp_required, lp_optional, {},
                            err_prefix + ' element ' + x)
        # TODO: Check if PascalCase or ALL_CAPS
        if not "type" in y:
            y["type"] = "int"

        if "local" in y:
            local, ierr = check_bool(y["local"], err_prefix + " local")
            if ierr:
                error += 1
                y["local"] = "true"
        else:
            y["local"] = "true"

        if "default" in y:
            if y["type"][:3] == "int":
                default, ierr = check_int(y["default"],
                                          err_prefix + " default")
                if ierr:
                    error += 1
                    y["default"] = "1"
        else:
            if y["type"][:3] == "int":
                y["default"] = "1"
            elif y["type"] == "string":
                y["default"] = ""
            else:
                log.err(err_prefix + ' element ' + x + '["' + y["name"] +
                        '"]' + ' type is not supported')
                return error + 1

    return error


def search_param(obj, key):
    """return the param object if found, else return non zero error
    """
    for p in obj:
        if p["name"] == key:
            return p, 0

    log.error("Param {} cannot be found".format(key))
    return None, 1


def check_keys(obj, required_keys, optional_keys, added_keys, err_prefix):
    error = 0
    for x in required_keys:
        if not x in obj:
            error += 1
            log.error(err_prefix + " missing required key " + x)
    for x in obj:
        type = ''
        if x in required_keys:
            type = required_keys[x][0]
        elif x in optional_keys:
            type = optional_keys[x][0]
        elif not x in added_keys:
            log.warning(err_prefix + " contains extra key " + x)
        if type[:2] == 'ln':
            error += check_ln(obj, x, type == 'lnw', err_prefix)
        if type == 'lp':
            error += check_lp(obj, x, err_prefix)

    return error


# Only allow zero or one of the list of keys
def check_zero_one_key(obj, optone, err_prefix):
    error = 0
    seenopt = 0
    for x in obj:
        if (x in optone):
            seenopt += 1
    if (seenopt > 1) or ((seenopt == 1) and len(obj) > 1):
        log.error(err_prefix + " only allowed one option key: ")
        for x in obj:
            log.error(err_prefix + "   found: " + x)
            error += 1
    return error


def bitfield_add(bfield, num):
    if ':' in bfield:
        brange = bfield.partition(':')
        msb = brange[0]
        lsb = brange[2]
        return str(int(msb) + num) + ':' + str(int(lsb) + num)
    else:
        return str(int(bfield) + num)


# get_bits to give a sort key
def get_bits(x):
    pos = x['bits'].find(':')
    if pos < 0:
        return int(x['bits'])
    else:
        return int(x['bits'][:pos])


# returns tuple (bitfield_mask, field width, lsb)
def bitmask(bfield):
    if ':' in bfield:
        brange = bfield.partition(':')
        msb = brange[0]
        lsb = brange[2]
        res = 0
        if ((not msb.isdecimal()) or (not lsb.isdecimal()) or
            (int(lsb) > int(msb))):
            log.error("Bad bit range " + bfield + str(brange))
            return (0, 0, 0)
        else:
            for i in range(int(lsb), int(msb) + 1):
                res |= (1 << i)
        return (res, int(msb) - int(lsb) + 1, int(lsb))
    if (not bfield.isdecimal()):
        log.error("Bad bit number " + bfield)
        return (0, 0, 0)
    else:
        return (1 << int(bfield), 1, int(bfield))


val_types = {
    'd': ["int", "integer (binary 0b, octal 0o, decimal, hex 0x)"],
    'x': ["xint", "x for undefined otherwise int"],
    'b': [
        "bitrange", "bit number as decimal integer, \
                    or bit-range as decimal integers msb:lsb"
    ],
    'l': ["list", "comma separated list enclosed in `[]`"],
    'ln': ["name list", 'comma separated list enclosed in `[]` of '\
           'one or more groups that have just name and dscr keys.'\
           ' e.g. `{ name: "name", desc: "description"}`'],
    'lnw': ["name list+", 'name list that optionally contains a width'],
    'lp': ["parameter list", 'parameter list having default value optionally'],
    'g': ["group", "comma separated group of key:value enclosed in `{}`"],
    'lg': ["list of group", "comma separated group of key:value enclosed in `{}`"\
           " the second entry of the list is the sub group format"],
    's': ["string", "string, typically short"],
    't': ["text", "string, may be multi-line enclosed in `'''` "\
          "may use `**bold**`, `*italic*` or `!!Reg` markup"],
    'T': ["tuple", "tuple enclosed in ()"],
    'pi': ["python int", "Native Python type int (generated)"],
    'pb': ["python Bool", "Native Python type Bool (generated)"],
    'pl': ["python list", "Native Python type list (generated)"],
    'pe': ["python enum", "Native Python type enum (generated)"]
}

# Toplevel keys
top_required = {
    'name': ['s', "name of the component"],
    'clock_primary': ['s', "name of the primary clock"],
    'bus_device': ['s', "name of the bus interface for the device"],
    'registers': [
        'l', "list of register definition groups and \
                              offset control groups"
    ]
}
top_optional = {
    'bus_host': ['s', "name of the bus interface as host"],
    'other_clock_list': ['l', "list of other chip clocks needed"],
    'available_input_list': ['lnw', "list of available peripheral inputs"],
    'available_output_list': ['lnw', "list of available peripheral outputs"],
    'available_inout_list': ['lnw', "list of available peripheral inouts"],
    'interrupt_list': ['lnw', "list of peripheral interrupts"],
    'no_auto_intr_regs': ['s', "Set to true to suppress automatic "\
                          "generation of interrupt registers. " \
                          "Defaults to false if not present."],
    'alert_list': ['lnw', "list of peripheral alerts"],
    'regwidth': ['d', "width of registers in bits (default 32)"],
    'param_list': ['lp', "list of parameters of the IP"],
    'scan': ['pb', 'Indicates the module have `scanmode_i`'],
    'SPDX-License-Identifier': ['s', "License ientifier (if using pure json) "\
                                "Only use this if unable to put this "\
                                "information in a comment at the top of the "\
                                "file."]
}
top_added = {'genrnames': ['pl', "list of register names"],
             'genautoregs': ['pb', "Registers were generated from config info"],
             'genwennames': ['pl', "list of registers used as write enables"],
             'gennextoffset': ['pi', "offset next register would use"],
             'gensize': ['pi', "address space size needed for registers. "\
                              "Generated by tool as next power of 2."]
             }

# ln type has list of groups with only name and description
# (was called "subunit" in cfg_validate)
ln_required = {
    'name': ['s', "name of the item"],
    'desc': ['s', "description of the item"],
}
ln_optional = {
    'width': ['d', "bit width of the item (if not 1)"],
}

# lp type
lp_required = {
    'name': ['s', "name of the item"],
}
lp_optional = {
    'desc': ['s', "description of the item"],
    'type': ['s', "item type. int by default"],
    'default': ['s', "item default value"],
    'local': ['pb', "to be localparam"],
}

# Registers list may have embedded keys
list_optone = {'reserved': ['d', "number of registers to reserve space for"],
              'skipto':    ['d', "set next register offset to value"],
              'sameaddr':  ['l', "list of register definition groups "\
                            "that share the same offset"],
              'window':    ['g', "group defining an address range "\
                            "for something other than standard registers"],
              'multireg':  ['g', "group defining registers generated "\
                            "from a base instance."]
               }

# Register keys
reg_required = {
    'name': ['s', "name of the register"],
    'desc': ['t', "description of the register"],
    'fields': ['l', "list of register field description groups"]
}

reg_optional = {
    'swaccess': [
        's', "software access permission to use for " +
        "fields that don't specify swaccess"
    ],
    'hwaccess': [
        's', "hardware access permission to use for " +
        "fields that don't specify hwaccess"
    ],
    'hwext': [
        's',
        "'true' if the register is stored out side " + "of the register module"
    ],
    'hwqe': [
        's', "'true' if hardware uses 'q' enable signal, " +
        "which is latched signal of software write pulse."
    ],
    'hwre': [
        's', "'true' if hardware uses 're' signal, " +
        "which is latched signal of software read pulse."
    ],
    'regwen': [
        's', "if register is write-protected by another register, that " +
        "register name should be given here. empty-string for no register " +
        "write protection"
    ],
    'resval': ['d', "reset value of full register (default 0)"]
}
reg_added = {
    'genresval': ['pi', "reset value generated from resval and fields"],
    'genresmask': ['pi', "mask of bits with valid reset value (not x)"],
    'genbitsused': ['pi', "mask of bits defined in the register"],
    'genoffset': ['pi', "offset address of the register"],
    'genbasebits': ['pi', "multireg only: mask of base bits defined"],
    'gendvrights': ['s', "SW Rights used in UVM reg class"]
}

# Window keys
window_required = {
    'name': ['s', "Name of the window"],
    'desc': ['t', "description of the window"],
    'items': ['d', "size in fieldaccess width words of the window"],
    'swaccess': ['s', "software access permitted"],
}

# TODO potential for additional optional to give more type info?
# eg sram-hw-port: "none", "sync", "async"
window_optional = {'byte-write': ['s', "True if byte writes are supported. "\
                                  "Defaults to false if not present."],
                   'validbits': ['d', "Number of valid data bits within "\
                                 "regwidth sized word. "\
                                 "Defaults to regwidth. If "\
                                 "smaller than the regwidth then in each "\
                                 "word of the window bits "\
                                 "[regwidth-1:validbits] are unused and "\
                                 "bits [validbits-1:0] are valid."],
                   'noalign': ['s', "Set to True to prevent tool aligning "\
                               "the base address of the window. "\
                               "Defaults to false if not present."],
                   'unusual': ['s', "True if window has unusual parameters "\
                               "(set to prevent Unusual: errors)."\
                               "Defaults to false if not present."]
                  }

window_added = {'genbyte-write': ['pb', "generated boolean for byte-write "],
                'genvalidbits': ['pi', "vailid data width"],
                'genoffset': ['pi', "base offset address of the window "\
                              "(aligned for size)"],
                'genswaccess': ['pe', "Software access (gen enum)"],
                'genswwraccess': ['pe', "Software write access (gen enum)"],
                'genswrdaccess': ['pe', "Software read access (gen enum)"]
               }

# Multireg keys
multireg_required = {'name':   ['s', "base name of the registers"],
                     'desc':   ['t', "description of the registers"],
                     'count':  ['s', "number of instances to generate."\
                                " This field can be integer or string matching"\
                                " from param_list"],
                     'cname':  ['s', "base name for each instance, mostly "\
                                "useful for refering to instance in messages"],
                     'fields': ['l', "list of register field description"\
                                "groups. Describes bit positions used for"\
                                " base instance."]
                     }
multireg_optional = reg_optional
multireg_optional.update({
    'regwen_incr': [
        's', "If true, regwen term increments along with current multireg " +
        "count "
    ],
})

multireg_added = {'genregs': ['l',
                              "generated list of registers with required "\
                              "and added keys"]
                  }

# Field keys
# special case in the code, no name and no desc if only field
field_required = {
    'name': ['s', "name of the field (optional if only field)"],
    'desc': ['t', "description of field (optional if no name)"],
    'bits': ['b', "bit or bit range (msb:lsb)"]
}
field_optional = {
    'swaccess': [
        's', "software access permission, copied from "
        "register if not provided in field. "
        "(Tool adds if not provided.)"
    ],
    'hwaccess': [
        's', "hardware access permission, copied from "
        "register if not prvided in field. "
        "(Tool adds if not provided.)"
    ],
    'resval': [
        'x', "reset value, comes from register resval "
        "if not provided in field. Zero if neither "
        "are provided and the field is readable, "
        "x if neither are provided and the field "
        "is wo. Must match if both are provided."
    ],
    'enum': ['l', "list of permitted enumeration groups"]
}
field_added = {
    'genrsvdenum': ['pb', "enum did not cover every possible value"],
    'genresval': [
        'pi', "resval for field constructed by the tool. "
        "Will be set to 0 for x."
    ],
    'genresvalx': ['pb', "Indicates if resval is x"],
    'genswaccess': ['pe', "Software access (generated enum)"],
    'genswwraccess': ['pe', "Software write access (generated enum)"],
    'genswrdaccess': ['pe', "Software read access (generated enum)"],
    'genhwaccess': ['pe', "Hardware access (generated Enum)"],
    'genhwqe': ['pb', "Hardware qualifier enable signal needed"],
    'genhwre': ['pb', "Hardware read enable signal needed"],
    'bitinfo': ['T', "tuple (bitfield_mask, field width, lsb)"]
}

# Enum keys
enum_required = {
    'name': ['s', "name of the member of the enum"],
    'desc': ['t', "description when field has this value"],
    'value': ['d', "value of this member of the enum"]
}
enum_optional = {}
enum_added = {}

# swaccess permitted values
# text description, access enum, wr access enum, rd access enum, ok in window
swaccess_permitted = {
    'ro':    ("Read Only",
                        SwAccess.RO,  SwWrAccess.NONE, SwRdAccess.RD,   True),
    'rc':    ("Read Only, reading clears",
                        SwAccess.RC,  SwWrAccess.WR,   SwRdAccess.RC,   False),
    'rw':    ("Read/Write",
                        SwAccess.RW,  SwWrAccess.WR,   SwRdAccess.RD,   True),
    'r0w1c': ("Read zero, Write with 1 clears",
                        SwAccess.W1C, SwWrAccess.WR,   SwRdAccess.NONE, False),
    'rw1s':  ("Read, Write with 1 sets",
                        SwAccess.W1S, SwWrAccess.WR,   SwRdAccess.RD,   False),
    'rw1c':  ("Read, Write with 1 clears",
                        SwAccess.W1C, SwWrAccess.WR,   SwRdAccess.RD,   False),
    'rw0c':  ("Read, Write with 0 clears",
                        SwAccess.W0C, SwWrAccess.WR,   SwRdAccess.RD,   False),
    'wo':    ("Write Only",
                        SwAccess.WO,  SwWrAccess.WR,   SwRdAccess.NONE, True)
} # yapf: disable

# hwaccess permitted values
hwaccess_permitted = {
    'hro': ("Read Only", HwAccess.HRO),
    'hrw': ("Read/Write", HwAccess.HRW),
    'hwo': ("Write Only", HwAccess.HWO),
    'none': ("No Access Needed", HwAccess.NONE)
}

key_use = {'r': "required", 'o': "optional", 'a': "added by tool"}

# Register name prohibited (used as reserved keywords in systemverilog)
keywords_verilog = [
    'alias', 'always', 'always_comb', 'always_ff', 'always_latch', 'and',
    'assert', 'assign', 'assume', 'automatic', 'before', 'begin', 'bind',
    'bins', 'binsof', 'bit', 'break', 'buf', 'bufif0', 'bufif1', 'byte',
    'case', 'casex', 'casez', 'cell', 'chandle', 'class', 'clocking', 'cmos',
    'config', 'const', 'constraint', 'context', 'continue', 'cover',
    'covergroup', 'coverpoint', 'cross', 'deassign', 'default', 'defparam',
    'design', 'disable', 'dist', 'do', 'edge', 'else', 'end', 'endcase',
    'endclass', 'endclocking', 'endconfig', 'endfunction', 'endgenerate',
    'endgroup', 'endinterface', 'endmodule', 'endpackage', 'endprimitive',
    'endprogram', 'endproperty', 'endspecify', 'endsequence', 'endtable',
    'endtask', 'enum', 'event', 'expect', 'export', 'extends', 'extern',
    'final', 'first_match', 'for', 'force', 'foreach', 'forever', 'fork',
    'forkjoin', 'function', 'generate', 'genvar', 'highz0', 'highz1', 'if',
    'iff', 'ifnone', 'ignore_bins', 'illegal_bins', 'import', 'incdir',
    'include', 'initial', 'inout', 'input', 'inside', 'instance', 'int',
    'integer', 'interface', 'intersect', 'join', 'join_any', 'join_none',
    'large', 'liblist', 'library', 'local', 'localparam', 'logic', 'longint',
    'macromodule', 'matches', 'medium', 'modport', 'module', 'nand', 'negedge',
    'new', 'nmos', 'nor', 'noshowcancelled', 'not', 'notif0', 'notif1', 'null',
    'or', 'output', 'package', 'packed', 'parameter', 'pmos', 'posedge',
    'primitive', 'priority', 'program', 'property', 'protected', 'pull0',
    'pull1', 'pulldown', 'pullup', 'pulsestyle_onevent', 'pulsestyle_ondetect',
    'pure', 'rand', 'randc', 'randcase', 'randsequence', 'rcmos', 'real',
    'realtime', 'ref', 'reg', 'release', 'repeat', 'return', 'rnmos', 'rpmos',
    'rtran', 'rtranif0', 'rtranif1', 'scalared', 'sequence', 'shortint',
    'shortreal', 'showcancelled', 'signed', 'small', 'solve', 'specify',
    'specparam', 'static', 'string', 'strong0', 'strong1', 'struct', 'super',
    'supply0', 'supply1', 'table', 'tagged', 'task', 'this', 'throughout',
    'time', 'timeprecision', 'timeunit', 'tran', 'tranif0', 'tranif1', 'tri',
    'tri0', 'tri1', 'triand', 'trior', 'trireg', 'type', 'typedef', 'union',
    'unique', 'unsigned', 'use', 'uwire', 'var', 'vectored', 'virtual', 'void',
    'wait', 'wait_order', 'wand', 'weak0', 'weak1', 'while', 'wildcard',
    'wire', 'with', 'within', 'wor', 'xnor', 'xor'
]


def validate_fields(fields, rname, default_sw, default_hw, full_resval,
                    reg_hwqe, reg_hwre, width):
    error = 0
    bits_used = 0
    gen_resval = 0
    gen_resmask = 0
    fcount = 0

    fieldnames = []
    if len(fields) == 0:
        log.warn(rname + " fields is empty")

    for field in fields:
        fcount += 1
        if not 'name' in field:
            fname = rname + ".field" + str(fcount)
            if (len(fields) == 1):
                field['name'] = rname
                # only allow no desc if no name
                if not 'desc' in field:
                    field['desc'] = ""
        else:
            fname = field['name']
            if fname in keywords_verilog:
                error += 1
                log.error(rname + " field " + fname + " uses Verilog keywords")
            if (fname == ""):
                fname = rname + ".field" + str(fcount)
            else:
                if fname in fieldnames:
                    error += 1
                    log.error(rname + " field " + str(fcount) +
                              ": duplicate use of field name " + fname)
                else:
                    fieldnames.append(fname)
                fname = rname + "." + fname
        ck_err = check_keys(field, field_required, field_optional, field_added,
                            fname)
        if (ck_err != 0):
            error += ck_err
            continue

        if not 'swaccess' in field:
            if (default_sw == None):
                error += 1
                log.error(fname + ":no swaccess or register default swaccess")
                swaccess = "wo"
            else:
                log.info(fname + ": use register default swaccess")
                field['swaccess'] = default_sw
                swaccess = default_sw
        else:
            swaccess = field['swaccess']
            if (not swaccess in swaccess_permitted):
                error += 1
                log.error(fname + ": Bad field swaccess value " + swaccess)
                swaccess = "wo"
        swacc_info = swaccess_permitted[swaccess]
        field['genswaccess'] = swacc_info[1]
        field['genswwraccess'] = swacc_info[2]
        field['genswrdaccess'] = swacc_info[3]

        if not 'hwaccess' in field:
            if (default_hw == None):
                error += 1
                log.error(fname + ": no hwaccess or register default hwaccess")
                hwaccess = "hro"
            else:
                log.info(fname + ": use register default hwaccess")
                field['hwaccess'] = default_hw
                hwaccess = default_hw
        else:
            hwaccess = field['hwaccess']
            if (not hwaccess in hwaccess_permitted):
                error += 1
                log.error(fname + ": Bad field hwaccess value " + hwaccess)
                hwaccess = "hro"
        hwacc_info = hwaccess_permitted[hwaccess]
        field['genhwaccess'] = hwacc_info[1]
        field['genhwqe'] = reg_hwqe
        field['genhwre'] = reg_hwre

        # allow an int but make a string for all downstream users
        if isinstance(field['bits'], int):
            field['bits'] = str(field['bits'])
        field_bits = bitmask(field['bits'])
        if (field_bits[0] == 0):
            error += 1
        else:
            reuse_check = bits_used & field_bits[0]
            # > is correct here because the check is of the bit
            # above the msb. The equal case is thus valid
            if ((field_bits[1] + field_bits[2]) > width):
                error += 1
                log.error(fname + ": Register not wide enough for bits: " +
                          field['bits'])
            elif reuse_check != 0:
                error += 1
                log.error(fname + ": Defines already defined bits " +
                          hex(reuse_check))
            bits_used |= field_bits[0]
            field['bitinfo'] = field_bits
        max_in_field = (1 << field_bits[1]) - 1

        if 'resval' in field:
            if field['resval'] != "x":
                resval, ierr = check_int(field['resval'], fname + " resval")
                if ierr:
                    error += 1
                if (resval > max_in_field):
                    error += 1
                    log.error(fname + ": Reset value " + field['resval'] +
                              " greater than max field can hold (" +
                              hex(max_in_field) + ")")
                    resval &= max_in_field

                if ((full_resval != None) and
                    (resval !=
                     ((full_resval >> field_bits[2]) & max_in_field))):
                    error += 1
                    log.error(fname + ": Field resval " + field['resval'] +
                              " differs from value in main register resval " +
                              hex(full_resval))
                gen_resval |= resval << field_bits[2]
                gen_resmask |= field_bits[0]
                field['genresval'] = resval
                field['genresvalx'] = False
            else:
                field['genresval'] = 0
                field['genresvalx'] = True
        else:
            if (full_resval != None):
                resval = (full_resval >> field_bits[2]) & max_in_field
                gen_resval |= resval << field_bits[2]
                gen_resmask |= field_bits[0]
                field['genresval'] = resval
                field['genresvalx'] = False
                log.info(fname + ": use register default genresval")
            else:
                if swaccess[0] != 'w':
                    field['genresval'] = 0
                    field['genresvalx'] = False
                    log.info(fname + ": use zero genresval")
                    gen_resmask |= field_bits[0]
                else:
                    field['genresval'] = 0
                    field['genresvalx'] = True
                    log.info(fname + ": use x genresval")

        if 'enum' in field:
            if max_in_field > 127:
                log.warning(fname + "enum too big for checking.")
                enum_mask = 0
            else:
                enum_mask = (1 << (max_in_field + 1)) - 1
            for enum in field['enum']:
                eck_err = check_keys(enum, enum_required, [], [],
                                     fname + " enum")
                if (eck_err != 0):
                    error += eck_err
                    continue
                ename = enum['name']
                val, ierr = check_int(enum['value'], fname + "." + ename)
                if ierr:
                    error += 1
                if (val > max_in_field):
                    error += 1
                    log.error(fname + ": enum value " + str(val) + "too big")
                elif max_in_field <= 127:
                    valbit = 1 << val
                    if ((enum_mask & valbit) == 0):
                        log.warning(fname + "enum has multiple " + str(val))
                    else:
                        enum_mask ^= valbit

            if (enum_mask != 0):
                field['genrsvdenum'] = True
                log.info(fname + ": Enum values not complete. Mask " +
                         hex(enum_mask))

    return error, gen_resval, gen_resmask, bits_used


def parse_dvrights(field=None):
    if field == None:
        return "RO"
    elif field in ['ro', 'rc']:
        return "RO"
    elif field in ['rw', 'r0w1c', 'rw1s', 'rw1c', 'rw0c']:
        return "RW"
    else:
        return "WO"


def validate_reg_defaults(reg, rname):
    error = 0
    if 'swaccess' in reg:
        default_sw = reg['swaccess']
        if (not default_sw in swaccess_permitted):
            error += 1
            log.error(rname + ": Bad register swaccess value " + default_sw)
            default_sw = None
    else:
        default_sw = None

    if 'hwaccess' in reg:
        default_hw = reg['hwaccess']
        if (not default_hw in hwaccess_permitted):
            error += 1
            log.error(rname + ": Bad register hwaccess value " + default_hw)
            default_hw = None
    else:
        default_hw = "hro"  # Read-Only

    if 'hwext' in reg:
        hwext, ierr = check_bool(reg['hwext'], rname + " hwext")
        if ierr:
            error += 1
            reg['hwext'] = "false"
    else:
        reg['hwext'] = "false"

    if 'hwqe' in reg:
        hwqe, ierr = check_bool(reg['hwqe'], rname + " hwqe")

        if ierr:
            error += 1
            reg['hwqe'] = "false"
        elif hwqe == False and reg[
                'hwext'] == "true" and reg['swaccess'] != "ro":
            log.warning(rname + ": hwqe must be true for hwext register. " +
                        "Changing it to true.")
            reg['hwqe'] = "true"
    elif reg['hwext'] == "true" and reg['swaccess'] != "ro":
        log.warning(rname + ": hwqe not provided but must be true for "\
                    "hwext not read-only register. Setting it to true.")
        reg['hwqe'] = "true"
    else:
        reg['hwqe'] = "false"

    if 'hwre' in reg:
        hwre, ierr = check_bool(reg['hwre'], rname + " hwre")

        if ierr:
            error += 1
            reg['hwre'] = "false"
        elif hwre == True and reg['hwext'] == "false":
            log.warning(rname + ": hwre cannot be used with hwext. " +
                        "Changing it to false.")
            reg['hwre'] = "false"
    else:
        reg['hwre'] = "false"

    if 'regwen' not in reg:
        reg['regwen'] = ''

    if 'resval' in reg:
        full_resval, ierr = check_int(reg['resval'], rname + " resval")
        if ierr:
            error += 1
            full_resval = None
    else:
        full_resval = None

    return error, default_sw, default_hw, full_resval


def validate_register(reg, offset, width, top):
    error = 0

    if not 'name' in reg:
        rname = "Register at +" + hex(offset)
    else:
        rname = reg['name']
        if rname in keywords_verilog:
            error += 1
            log.error("Register at +" + hex(offset) + rname +
                      " uses Verilog keywords")
        if rname.lower() in top['genrnames']:
            error += 1
            log.error("Register at +" + hex(offset) + " duplicate name " +
                      rname)
        else:
            top['genrnames'].append(rname.lower())

    error += check_keys(reg, reg_required, reg_optional, reg_added, rname)

    derr, default_sw, default_hw, full_resval = validate_reg_defaults(
        reg, rname)
    error += derr

    # if there was an error before this then can't trust anything!
    if error > 0:
        log.info(rname + "@" + hex(offset) + " " + str(error) +
                 " top level errors. Not processing fields")
        return error

    gen = validate_fields(reg['fields'], rname, default_sw, default_hw,
                          full_resval, reg['hwqe'] == "true",
                          reg['hwre'] == "true", width)
    error = error + gen[0]
    # ensure the fields are in order (except if error which could be bad bits)
    if error == 0:
        reg['fields'].sort(key=get_bits)
    reg['genresval'] = gen[1]
    reg['genresmask'] = gen[2]
    reg['genbitsused'] = gen[3]
    reg['genoffset'] = offset
    reg['gendvrights'] = parse_dvrights(default_sw)

    if ((reg['regwen'] != '') and (not reg['regwen'] in top['genwennames'])):
        top['genwennames'].append(reg['regwen'])

    log.info(rname + "@" + hex(offset) + " " + str(error) + " errors. Mask " +
             hex(gen[3]))

    return error


def validate_multi(mreg, offset, addrsep, width, top):
    error = 0
    bits_used = 0

    if not 'name' in mreg:
        mrname = "MultiRegister at +" + hex(offset)
        mreg["name"] = "MREG_" + hex(offset)
    else:
        mrname = mreg['name']
    error = check_keys(mreg, multireg_required, multireg_optional,
                       multireg_added, mrname)
    derr, default_sw, default_hw, full_resval = validate_reg_defaults(
        mreg, mrname)
    error += derr

    # multireg specific default validation
    regwen_incr = False
    if 'regwen_incr' not in mreg or 'regwen' not in mreg:
        mreg['regwen_incr'] = 'false'
    else:
        regwen_incr, derr = check_bool(mreg['regwen_incr'],
                                       mrname + " multireg increment")
        error += derr

    # if there was an error before this then can't trust anything!
    if error > 0:
        log.info(mrname + "@" + hex(offset) + " " + str(error) +
                 " top level errors. Not processing fields")
        return error

    gen = validate_fields(mreg['fields'], mrname, default_sw, default_hw,
                          full_resval, mreg['hwqe'] == "true",
                          mreg['hwre'] == "true", width)

    error += gen[0]

    # Check `count` field if it is in paramter list
    # If count is integer, add the value to param with name as REGISTER
    mcount, ierr = check_count(top, mreg, mrname + " multireg count")
    if ierr:
        error += 1

    if error > 0:
        return (error, 0)
    bused = gen[3]
    max_rval = (1 << width) - 1
    cname = mreg['cname']
    bpos = 0
    inum = 0
    rlist = []
    rnum = 0
    while inum < mcount:
        closereg = False
        if bpos == 0:
            genreg = {}
            genreg['name'] = mrname + str(rnum)
            genreg['desc'] = mreg['desc']
            genreg['hwext'] = mreg['hwext']
            genreg['hwqe'] = mreg['hwqe']
            genreg['hwre'] = mreg['hwre']
            genreg['swaccess'] = default_sw
            genreg['hwaccess'] = default_hw

            if regwen_incr:
                genreg['regwen'] = mreg['regwen'] + str(rnum)
            else:
                genreg['regwen'] = mreg['regwen']

            resval = 0
            resmask = 0
            bits_used = 0
            genfields = []

        while bpos < width:
            trypos = bused << bpos
            if trypos > max_rval:
                bpos = width
                break
            if (trypos & bits_used) == 0:
                break
            bpos += 1
        if bpos < width:
            # found a spot
            for fn in mreg['fields']:
                newf = fn.copy()
                newf['name'] += str(inum)
                if bpos != 0:
                    newf['bits'] = bitfield_add(newf['bits'], bpos)
                    newf['desc'] = 'for ' + cname + str(inum)
                    newf['bitinfo'] = (newf['bitinfo'][0] << bpos,
                                       newf['bitinfo'][1],
                                       newf['bitinfo'][2] + bpos)
                    if 'enum' in newf:
                        del newf['enum']
                else:
                    newf['desc'] += ' for ' + cname + str(inum)
                genfields.append(newf)
            bits_used = bits_used | bused << bpos
            resval = resval | gen[1] << bpos
            resmask = resmask | gen[2] << bpos
            bpos += 1
            inum += 1
            if inum == mcount:
                closereg = True
        else:
            # need new register
            closereg = True

        if closereg:
            genreg['fields'] = genfields
            genreg['genbasebits'] = bused
            error += validate_register(genreg, offset + (rnum * addrsep),
                                       width, top)
            if error:
                return (error, 0)
            rnum += 1
            bpos = 0
            rlist.append(genreg)
    # there is only one entry, so the index is unnecessary.  Pop and re-assign names
    # associated with the index
    if len(rlist) == 1:
        if regwen_incr:
            error += 1
            log.error(
                "%s multireg has only 1 register entry with regwen_incr set to true"
                % mrname)
        # TODO really should make the following a function that reverses the last node inserted
        # may have more properties than just genrnames in the future
        rlist[0]['name'] = mrname
        rlist[0]['regwen'] = mreg['regwen']
        top['genrnames'].pop()
    mreg['genregs'] = rlist
    top['genrnames'].append(mrname.lower())
    return error, rnum


def make_intr_reg(regs, name, offset, swaccess, hwaccess, desc):
    intrs = regs['interrupt_list']
    genreg = {}
    genreg['name'] = name
    genreg['desc'] = desc
    genreg['hwext'] = 'true' if name == 'INTR_TEST' else 'false'
    genreg['hwqe'] = 'true' if name == 'INTR_TEST' else 'false'
    genreg['hwre'] = 'false'
    bits_used = 0
    genfields = []
    cur_bit = 0
    for bit in intrs:
        newf = {}
        newf['name'] = bit['name']
        w = 1
        if 'width' in bit and bit['width'] != '1':
            w = int(bit['width'], 0)
            newf['bits'] = str(cur_bit + w - 1) + ':' + str(cur_bit)
            newf['bitinfo'] = (((1 << w) - 1) << cur_bit, w, cur_bit)
        else:
            newf['bits'] = str(cur_bit)
            newf['bitinfo'] = (1 << cur_bit, 1, cur_bit)
        if name == 'INTR_ENABLE':
            newf['desc'] = 'Enable interrupt when ' + \
                           ('corresponding bit in ' if w > 1 else '') + \
                           '!!INTR_STATE.' + newf['name'] + ' is set'
        elif name == 'INTR_TEST':
            newf['desc'] = 'Write 1 to force ' + \
                           ('corresponding bit in ' if w > 1 else '') + \
                           '!!INTR_STATE.' + newf['name'] + ' to 1'
        else:
            newf['desc'] = bit['desc']
        newf['swaccess'] = swaccess
        swacc_info = swaccess_permitted[swaccess]
        newf['genswaccess'] = swacc_info[1]
        newf['genswwraccess'] = swacc_info[2]
        newf['genswrdaccess'] = swacc_info[3]
        newf['hwaccess'] = hwaccess
        hwacc_info = hwaccess_permitted[hwaccess]
        newf['genhwaccess'] = hwacc_info[1]
        newf['genhwqe'] = True if name == 'INTR_TEST' else False
        newf['genhwre'] = False
        newf['genresval'] = 0
        newf['genresvalx'] = False

        bits_used = bits_used | (1 << cur_bit)
        cur_bit += 1
        genfields.append(newf)

    genreg['genresval'] = 0
    genreg['genresmask'] = bits_used
    genreg['genbitsused'] = bits_used
    genreg['genoffset'] = offset
    genreg['gendvrights'] = parse_dvrights(swaccess)
    genreg['fields'] = genfields
    genreg['regwen'] = ''
    regs['genrnames'].append(name.lower())
    return genreg


def make_intr_regs(regs, offset, addrsep, fullwidth):
    iregs = []
    intrs = regs['interrupt_list']
    if sum([int(x['width'], 0) if 'width' in x else 1
            for x in intrs]) > fullwidth:
        log.error('More than ' + str(fullwidth) + ' interrupts in list')
        return iregs, 1

    iregs.append(
        make_intr_reg(regs, 'INTR_STATE', offset, 'rw1c', 'hrw',
                      'Interrupt State Register'))
    iregs.append(
        make_intr_reg(regs, 'INTR_ENABLE', offset + addrsep, 'rw', 'hro',
                      'Interrupt Enable Register'))
    iregs.append(
        make_intr_reg(regs, 'INTR_TEST', offset + 2 * addrsep, 'wo', 'hro',
                      'Interrupt Test Register'))
    return iregs, 0


def validate_window(win, offset, regwidth, top):
    error = 0

    if not 'name' in win:
        name = "Window at +" + hex(offset)
    else:
        name = win['name']
        if name.lower() in top['genrnames']:
            error += 1
            log.error("Window at +" + hex(offset) + " duplicate name " + name)
        else:
            top['genrnames'].append(name.lower())

    error += check_keys(win, window_required, window_optional, window_added,
                        name)

    # if there was an error before this then can't trust anything!
    if error > 0:
        log.info(name + "@" + hex(offset) + " " + str(error) +
                 " top level errors. Window will be ignored.")
        return error, offset

    # optional flags
    unusual = 'unusual' in win and win['unusual'].lower() == "true"
    noalign = 'noalign' in win and win['noalign'].lower() == "true"
    win['genbyte-write'] = ('byte-write' in win and
                            win['byte-write'].lower() == "true")

    if 'validbits' in win:
        wid, err = check_int(win['validbits'], name + " validbits")
        if err:
            error += err
            wid = regwidth
        if wid > regwidth:
            error += 1
            log.error(name + ": validbits " + str(wid) +
                      " is greater than regwidth (" + str(regwidth) + ").")
            wid = regwidth
        win['genvalidbits'] = wid
    else:
        win['genvalidbits'] = regwidth

    winitems, err = check_int(win['items'], name + " items")
    if err:
        error += err
        winitems = 4
    # convert items to bytes
    winsize = winitems * (regwidth // 8)
    # if size is not a power of two, po2_size is next po2 larger
    po2_size = 1 << (winsize.bit_length() - 1)
    if winsize != po2_size:
        # the -1 above was wrong if not a power of two
        po2_size = po2_size << 1
        if not unusual:
            log.warn(name + ": Unusual: Size " + str(winitems) +
                     " is not a power of 2.")

    if noalign:
        genoff = offset
        nextoff = offset + winsize
    else:
        # Align to ensure base address of first item in window has
        # all zeros in the low bits
        if (offset & (po2_size - 1)) != 0:
            genoff = (offset | (po2_size - 1)) + 1
        else:
            genoff = offset
        nextoff = genoff + winsize
    win['genoffset'] = genoff

    swaccess = win['swaccess']
    if (not swaccess in swaccess_permitted):
        log.warn(name + ": Bad window swaccess value " + swaccess)
        swaccess = "wo"
    swacc_info = swaccess_permitted[swaccess]
    win['genswaccess'] = swacc_info[1]
    win['genswwraccess'] = swacc_info[2]
    win['genswrdaccess'] = swacc_info[3]
    if not swacc_info[4] and not unusual:
        log.warn(name + ": Unusual: access type for a window " + swaccess)

    return error, nextoff


""" Check that terms specified for regwen exist

Regwen can be individual registers or fields within a register.  The function
below checks for both and additional regwen properties.
"""


def check_wen_regs(regs):
    error = 0
    idx = 0

    # Construct Tuple
    # 0 - name
    # 1 - reset value
    # 2 - sw access
    tuple_name = 0
    tuple_rstval = 1
    tuple_swaccess = 2

    reg_list = [(reg['name'].lower(), reg['genresval'], reg['swaccess'])
                for reg in regs['registers']
                if 'name' in reg and 'genresval' in reg]
    mreg_list = [
        reg['multireg'] for reg in regs['registers'] if 'multireg' in reg
    ]
    field_list = [((reg['name'] + "_" + field['name']).lower(),
                   field['genresval'], field['swaccess']) for mreg in mreg_list
                  for reg in mreg['genregs'] for field in reg['fields']]

    # Need to check in register names and field list in case of multireg
    reg_list.extend(field_list)

    # check for reset value
    # both w1c and w0c are acceptable
    for x in regs['genwennames']:
        target = x.lower()
        log.info("check_wen_regs::Searching for %s" % target)
        try:
            idx = [r[tuple_name] for r in reg_list].index(target)
        except ValueError:
            log.error("Could not find register name matching %s" % target)

        if not reg_list[idx][tuple_rstval]:
            error += 1
            log.error(x + " used as regwen fails requirement to default " +
                      "to 1")

        if not reg_list[idx][tuple_swaccess] in ["rw0c", "rw1c"]:
            error += 1
            log.error(x +
                      " used as regwen fails requirement to be W1C or W0C ")

    return error


def validate(regs, **kwargs):
    if "params" in kwargs:
        params = kwargs["params"]
    else:
        params = []

    if not 'name' in regs:
        log.error("Component has no name. Aborting.")
        return 1
    component = regs['name']

    error = check_keys(regs, top_required, top_optional, top_added, component)
    if (error > 0):
        log.error("Component has top level errors. Aborting.")
        return error
    regs['genrnames'] = []
    regs['genwennames'] = []
    error = 0

    if 'regwidth' in regs:
        fullwidth, ierr = check_int(regs['regwidth'], "regwidth")
        if ierr:
            fullwidth = 32
            error += 1
    else:
        fullwidth = 32
        log.warning('regwidth not specified, assuming 32.')
    regs['regwidth'] = str(fullwidth)

    if ((fullwidth % 8) != 0):
        addrsep = (fullwidth // 8) + 1
        log.warning("regwidth is not a multiple of 8 bits!")
    else:
        addrsep = fullwidth // 8

    offset = 0
    autoregs = []

    # auto header generation would go here and update autoregs

    if 'no_auto_intr_regs' in regs:
        no_autoi, err = check_bool(regs['no_auto_intr_regs'],
                                   'no_auto_intr_regs')
        if err:
            error += 1
    else:
        no_autoi = False
    if 'interrupt_list' in regs and not 'genautoregs' in regs and not no_autoi:
        iregs, err = make_intr_regs(regs, offset, addrsep, fullwidth)
        error += err
        autoregs.extend(iregs)
        offset += addrsep * len(iregs)

    # Change default param value if exists.
    #   Assumed param list is already validated in above `check_keys` function
    if "param_list" in regs and len(regs["param_list"]) != 0:
        for p in params:
            if p == '':
                continue

            tokens = p.split('=')
            if len(tokens) != 2:
                error += 1
                log.error("Parameter format isn't correct. {}".format(p))
            key, value = tokens[0], tokens[1]
            param, err = search_param(regs["param_list"], key)
            if err != 0:
                error += err
                continue

            value, err = check_int(
                value, component + " param[{}]".format(param["name"]))
            if err != 0:
                error += err
                continue

            param["default"] = value

    if "scan" in regs:
        scan, err = check_bool(regs["scan"], component + " scan")
    else:
        regs["scan"] = "false"

    for x in regs['registers']:
        ck_err = check_zero_one_key(x, list_optone, "At " + hex(offset))
        if ck_err != 0:
            error += ck_err
            continue

        if 'reserved' in x:
            nreserved, ierr = check_int(x['reserved'],
                                        "Reserved at " + hex(offset))
            if ierr:
                error += 1
            else:
                offset = offset + (addrsep * nreserved)
            continue

        if 'skipto' in x:
            skipto, ierr = check_int(x['skipto'], "skipto at " + hex(offset))
            if ierr:
                error += 1
            elif (skipto < offset):
                log.error("{skipto " + x['skipto'] + "} at " + hex(offset) +
                          " evaluates as " + hex(skipto) +
                          " which would move backwards")
                error += 1
            elif (skipto % addrsep) != 0:
                log.error("{skipto " + x['skipto'] + "} at " + hex(offset) +
                          " evaluates as " + hex(skipto) +
                          " which is not a multiple of the register size " +
                          str(addrsep))
                error += 1
            else:
                offset = skipto
            continue

        if 'sameaddr' in x:
            for sareg in x['sameaddr']:
                error += validate_register(sareg, offset, fullwidth, regs)
            offset += addrsep
            continue

        if 'window' in x:
            err, offset = validate_window(x['window'], offset, fullwidth, regs)
            error += err
            continue

        if 'multireg' in x:
            err, n = validate_multi(x['multireg'], offset, addrsep, fullwidth,
                                    regs)
            error += err
            offset += addrsep * n
            continue

        error += validate_register(x, offset, fullwidth, regs)
        offset += addrsep
    regs['gennextoffset'] = offset
    # make the right thing happen if now exactly on power of 2
    if (offset > 0): offset -= 1
    regs['gensize'] = 1 << offset.bit_length()

    error += check_wen_regs(regs)

    if autoregs:
        # auto generated registers go at the front
        autoregs.extend(regs['registers'])
        regs['registers'] = autoregs
        regs['genautoregs'] = True

    log.info("Validated, size = " + hex(regs['gensize']) + " errors=" +
             str(error) + " names are " + str(regs['genrnames']))
    if (error > 0):
        log.error("Register description had " + str(error) + " error" +
                  "s" if error > 1 else "")
    return error
