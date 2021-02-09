# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Register JSON validation
"""

import logging as log
import re
from collections import OrderedDict

from .access import SWAccess, HWAccess
from .bits import Bits
from .field import Field
from .multi_register import MultiRegister
from .register import Register
from .window import Window


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


# validating version of int(x, 0)
# returns int value, error flag
# if error flag is True value will be zero
def check_int(x, err_prefix, suppress_err_msg=False):
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
            if not suppress_err_msg:
                log.error(err_prefix +
                          ": int must start digit, 0b, 0B, 0o, 0O, 0x or 0X")
            return 0, True
        for c in x[2:]:
            if c not in validch:
                if not suppress_err_msg:
                    log.error(err_prefix + ": Bad character " + c + " in " + x)
                return 0, True
    else:
        if not x.isdecimal():
            if not suppress_err_msg:
                log.error(err_prefix + ": Number not valid int " + x)
            return 0, True
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

        # If this is a random netlist constant, other attributes like local, default and expose
        # are automatically set. Throw an error if they already exist in the dict.
        randcount = int(y.setdefault('randcount', "0"))
        randtype = y.setdefault('randtype', "none")
        if randtype != "none":

            if randcount <= 0:
                log.error(err_prefix + ' randwith for parameter ' + y['name'] +
                          ' must be greater > 0.')
                return error + 1

            if randtype not in ['perm', 'data']:
                log.error(err_prefix + ' parameter ' + y['name'] +
                          ' has unknown randtype ' + randtype)
                return error + 1

            if y.get('type') is None:
                log.error(
                    err_prefix + ' parameter ' + y['name'] +
                    ' has undefined type. '
                    'It is required to define the type in the IP package.')
                return error + 1

            if not y.get('name').lower().startswith('rndcnst'):
                log.error(
                    err_prefix + ' parameter ' + y['name'] +
                    ' is defined as a compile-time '
                    'random netlist constant. The name must therefore start with RndCnst.'
                )
                return error + 1

            overrides = [('local', 'false'), ('default', ''),
                         ('expose', 'false')]

            for key, value in overrides:
                if y.setdefault(key, value) != value:
                    log.error(
                        err_prefix + ' ' + key + ' for parameter ' +
                        y['name'] +
                        ' must not be set since it will be defined automatically.'
                    )
                    return error + 1

        # TODO: Check if PascalCase or ALL_CAPS
        y.setdefault('type', 'int')

        y.setdefault('local', 'true')
        local, ierr = check_bool(y["local"], err_prefix + " local")
        if ierr:
            error += 1
            y["local"] = "true"

        y.setdefault('expose', 'false')
        local, ierr = check_bool(y["expose"], err_prefix + " expose")
        if ierr:
            error += 1
            y["expose"] = "false"

        if y["local"] == "true" and y["expose"] == "true":
            log.error(err_prefix + ' element ' + x + '["' + y["name"] + '"]' +
                      ' cannot be local and exposed to top level')
            return error + 1

        if "default" in y:
            if y["type"][:3] == "int":
                default, ierr = check_int(y["default"],
                                          err_prefix + " default")
                if ierr:
                    error += 1
                    y["default"] = "1"
        elif y["randtype"] != "none":
            # Don't make assumptions for exposed parameters. These must have
            # a default.
            if y["expose"] == "true":
                log.error(err_prefix + ' element ' + x + '["' + y["name"] +
                          '"]' + ' has no defined default value')
            elif y["type"][:3] == "int":
                y["default"] = "1"
            elif y["type"] == "string":
                y["default"] = ""
            else:
                log.error(err_prefix + ' element ' + x + '["' + y["name"] +
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
        if x not in obj:
            error += 1
            log.error(err_prefix + " missing required key " + x)
    for x in obj:
        type = None
        if x in required_keys:
            type = required_keys[x][0]
        elif x in optional_keys:
            type = optional_keys[x][0]
        elif x not in added_keys:
            log.warning(err_prefix + " contains extra key " + x)
        if type is not None:
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


val_types = {
    'd': ["int", "integer (binary 0b, octal 0o, decimal, hex 0x)"],
    'x': ["xint", "x for undefined otherwise int"],
    'b': [
        "bitrange", "bit number as decimal integer, "
        "or bit-range as decimal integers msb:lsb"
    ],
    'l': ["list", "comma separated list enclosed in `[]`"],
    'ln': [
        "name list", 'comma separated list enclosed in `[]` of '
        'one or more groups that have just name and dscr keys.'
        ' e.g. `{ name: "name", desc: "description"}`'
    ],
    'lnw': ["name list+", 'name list that optionally contains a width'],
    'lp': ["parameter list", 'parameter list having default value optionally'],
    'g': ["group", "comma separated group of key:value enclosed in `{}`"],
    'lg': [
        "list of group", "comma separated group of key:value enclosed in `{}`"
        " the second entry of the list is the sub group format"
    ],
    's': ["string", "string, typically short"],
    't': [
        "text", "string, may be multi-line enclosed in `'''` "
        "may use `**bold**`, `*italic*` or `!!Reg` markup"
    ],
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
    'registers':
    ['l', "list of register definition groups and "
     "offset control groups"]
}
top_optional = {
    'alert_list': ['lnw', "list of peripheral alerts"],
    'available_inout_list': ['lnw', "list of available peripheral inouts"],
    'available_input_list': ['lnw', "list of available peripheral inputs"],
    'available_output_list': ['lnw', "list of available peripheral outputs"],
    'bus_host': ['s', "name of the bus interface as host"],
    'hier_path': [
        None,
        'additional hierarchy path before the reg block instance'
    ],
    'interrupt_list': ['lnw', "list of peripheral interrupts"],
    'inter_signal_list': ['l', "list of inter-module signals"],
    'no_auto_alert_regs': [
        's', "Set to true to suppress automatic "
        "generation of alert test registers. "
        "Defaults to true if no alert_list is present. "
        "Otherwise this defaults to false. "
    ],
    'no_auto_intr_regs': [
        's', "Set to true to suppress automatic "
        "generation of interrupt registers. "
        "Defaults to true if no interrupt_list is present. "
        "Otherwise this defaults to false. "
    ],
    'other_clock_list': ['l', "list of other chip clocks needed"],
    'other_reset_list': ['l', "list of other resets"],
    'param_list': ['lp', "list of parameters of the IP"],
    'regwidth': ['d', "width of registers in bits (default 32)"],
    'reset_primary': ['s', "primary reset used by the module"],
    'reset_request_list': ['l', 'list of signals requesting reset'],
    'scan': ['pb', 'Indicates the module have `scanmode_i`'],
    'scan_reset': ['pb', 'Indicates the module have `test_rst_ni`'],
    'SPDX-License-Identifier': [
        's', "License ientifier (if using pure json) "
        "Only use this if unable to put this "
        "information in a comment at the top of the "
        "file."
    ],
    'wakeup_list': ['lnw', "list of peripheral wakeups"]
}
top_added = {
    'genrnames': ['pl', "list of register names"],
    'genautoregs': ['pb', "Registers were generated from config info"],
    'genwennames': ['pl', "list of registers used as write enables"],
    'gennextoffset': ['pi', "offset next register would use"],
    'gensize': [
        'pi', "address space size needed for registers. "
        "Generated by tool as next power of 2."
    ]
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
    'expose': ['pb', "to be exposed to top"],
    'randcount':
    ['s', "number of bits to randomize in the parameter. 0 by default."],
    'randtype': ['s', "type of randomization to perform. none by default"],
}

# Registers list may have embedded keys
list_optone = {
    'reserved': ['d', "number of registers to reserve space for"],
    'skipto': ['d', "set next register offset to value"],
    'window': [
        'g', "group defining an address range "
        "for something other than standard registers"
    ],
    'multireg':
    ['g', "group defining registers generated "
     "from a base instance."]
}

key_use = {'r': "required", 'o': "optional", 'a': "added by tool"}


def _upd_regnames(regs, offset, register):
    genrnames = regs['genrnames']
    rname = register.name.lower()
    err = 0
    if rname in genrnames:
        log.error('Duplicate register name {!r} at offset {:#x}.'
                  .format(offset, rname))
        err = 1
    genrnames.append(rname)
    genwennames = regs['genwennames']
    if register.regwen is not None and register.regwen not in genwennames:
        genwennames.append(register.regwen)

    return err


def make_intr_alert_reg(regs, name, offset, swaccess, hwaccess, desc):
    if name == 'ALERT_TEST':
        signal_list = regs['alert_list']
    else:
        signal_list = regs['interrupt_list']
    # these names will be converted into test registers
    testreg_names = ['INTR_TEST', 'ALERT_TEST']

    swaccess_obj = SWAccess('make_intr_alert_reg()', swaccess)
    hwaccess_obj = HWAccess('make_intr_alert_reg()', hwaccess)

    fields = []
    cur_bit = 0
    for (field_idx, bit) in enumerate(signal_list):
        w = 1
        if 'width' in bit and bit['width'] != '1':
            w = int(bit['width'], 0)
            field_bits = Bits(cur_bit + w - 1, cur_bit)
        else:
            field_bits = Bits(cur_bit, cur_bit)
        cur_bit += w

        field_name = bit['name']
        if name == 'INTR_ENABLE':
            field_desc = ('Enable interrupt when {}!!INTR_STATE.{} is set.'
                          .format('corresponding bit in ' if w > 1 else '',
                                  field_name))
        elif name == 'INTR_TEST':
            field_desc = ('Write 1 to force {}!!INTR_STATE.{} to 1.'
                          .format('corresponding bit in ' if w > 1 else '',
                                  field_name))
        elif name == 'ALERT_TEST':
            field_desc = 'Write 1 to trigger one alert event of this kind.'
        else:
            field_desc = bit['desc']

        # Put the automatically generated information back into
        # `interrupt_list`, so that it can be used to generate C preprocessor
        # definitions if needed.
        signal_list[field_idx]['bits'] = field_bits.as_str()
        signal_list[field_idx]['bitinfo'] = (field_bits.bitmask(),
                                             field_bits.width(),
                                             field_bits.lsb)

        fields.append(Field(field_name,
                            field_desc,
                            bit.get('tags', []),
                            swaccess_obj,
                            hwaccess_obj,
                            hwqe=name in testreg_names,
                            hwre=False,
                            bits=field_bits,
                            resval=0,
                            enum=None))

    hwext = 'true' if name in testreg_names else 'false'
    if name == 'INTR_TEST':
        # intr_test csr is WO which - it reads back 0s
        reg_tags = ["excl:CsrNonInitTests:CsrExclWrite"]
    elif name == 'INTR_STATE':
        # intr_state csr is affected by writes to other csrs - skip write-check
        reg_tags = ["excl:CsrNonInitTests:CsrExclWriteCheck"]
    else:
        reg_tags = []

    bool_hwext = hwext.lower() == 'true'

    reg = Register(offset,
                   name,
                   desc,
                   swaccess_obj,
                   hwaccess_obj,
                   hwext=bool_hwext,
                   hwqe=bool_hwext,
                   hwre=False,
                   regwen=None,
                   tags=reg_tags,
                   resval=None,
                   shadowed=False,
                   fields=fields,
                   update_err_alert=None,
                   storage_err_alert=None)
    _upd_regnames(regs, offset, reg)
    return reg


def make_intr_regs(regs, offset, addrsep, fullwidth):
    iregs = []
    intrs = regs['interrupt_list']
    num_intrs = sum([int(x.get('width', '1'), 0) for x in intrs])
    if num_intrs > fullwidth:
        log.error('More than ' + str(fullwidth) + ' interrupts in list')
        return iregs, 1

    new_reg = make_intr_alert_reg(regs, 'INTR_STATE', offset, 'rw1c', 'hrw',
                                  'Interrupt State Register')
    iregs.append(new_reg)
    new_reg = make_intr_alert_reg(regs, 'INTR_ENABLE', offset + addrsep, 'rw',
                                  'hro', 'Interrupt Enable Register')
    iregs.append(new_reg)
    new_reg = make_intr_alert_reg(regs, 'INTR_TEST', offset + 2 * addrsep,
                                  'wo', 'hro', 'Interrupt Test Register')
    iregs.append(new_reg)
    return iregs, 0


def make_alert_regs(regs, offset, addrsep, fullwidth):
    alert_regs = []
    alerts = regs['alert_list']
    num_alerts = sum([int(x.get('width', '1'), 0) for x in alerts])
    if num_alerts > fullwidth:
        log.error('More than ' + str(fullwidth) + ' alerts in list')
        return alert_regs, 1

    new_reg = make_intr_alert_reg(regs, 'ALERT_TEST', offset, 'wo', 'hro',
                                  'Alert Test Register')
    alert_regs.append(new_reg)
    return alert_regs, 0


""" Check that terms specified for regwen exist

Regwen are all assumed to be individual registers.
"""


def check_wen_regs(regs):
    error = 0

    # Construct a map from register name to a tuple (resval, swaccess, hwaccess)
    name_to_reg_data = {}
    for x in regs['registers']:
        if isinstance(x, Register):
            x_regs = [x]
        elif isinstance(x, MultiRegister):
            x_regs = x.regs
        else:
            x_regs = []

        for reg in x_regs:
            assert isinstance(reg, Register)
            reg_data = (reg.resval, reg.swaccess, reg.hwaccess)
            name_to_reg_data[reg.name.lower()] = reg_data

    # check for reset value
    # both w1c and w0c are acceptable, ro is also acceptable when hwaccess is wo (hw managed regwen)
    for x in regs['genwennames']:

        # check the REGWEN naming convention
        if re.fullmatch(r'(.+_)*REGWEN(_[0-9]+)?', x) is None:
            error += 1
            log.error("Regwen name %s must have the suffix '_REGWEN'" % x)

        target = x.lower()
        log.debug("check_wen_regs::Searching for %s" % target)

        reg_data = name_to_reg_data.get(target)
        if reg_data is None:
            error += 1
            log.error("Could not find register name matching %s" % target)
            continue

        resval, swaccess, hwaccess = reg_data

        # If the REGWEN bit is SW controlled, enfore that this bit defaults to 1.
        # If this bit is read-only by SW and hence hardware controlled, we do
        # not enforce this requirement.
        if swaccess.key != "ro" and not resval:
            error += 1
            log.error(x + " used as regwen fails requirement to default " +
                      "to 1")

        # either the regwen is software managed (must be rw0c)
        # or it is completely hw managed (sw=r0 and hw=wo)
        sw_regwen = 0
        hw_regwen = 0

        if swaccess.key in ["rw0c"]:
            sw_regwen += 1

        if swaccess.key == "ro" and hwaccess.key == "hwo":
            hw_regwen += 1

        if (sw_regwen + hw_regwen) == 0:
            error += 1
            log.error(
                "{x} used as regwen fails requirement to be "
                "swaccess=RW0C or swaccess=RO and hwaccess=HWO".format(x=x))

    return error


def validate(regs, **kwargs):
    if "params" in kwargs:
        params = kwargs["params"]
    else:
        params = []

    if 'name' not in regs:
        log.error("Component has no name. Aborting.")
        return 1

    component = regs['name']

    regs.setdefault('param_list', [])

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
        no_auto_intr, err = check_bool(regs['no_auto_intr_regs'],
                                       'no_auto_intr_regs')
        if err:
            error += 1
    else:
        if 'interrupt_list' not in regs:
            no_auto_intr = True
        else:
            no_auto_intr = False

    if 'no_auto_alert_regs' in regs:
        no_auto_alerts, err = check_bool(regs['no_auto_alert_regs'],
                                         'no_auto_alert_regs')
        if err:
            error += 1
    else:
        if 'alert_list' not in regs:
            no_auto_alerts = True
        else:
            no_auto_alerts = False

    if 'interrupt_list' in regs and 'genautoregs' not in regs and not no_auto_intr:
        iregs, err = make_intr_regs(regs, offset, addrsep, fullwidth)
        error += err
        autoregs.extend(iregs)
        offset += addrsep * len(iregs)

    # Generate a NumAlerts parameter for provided alert_list.
    if regs.setdefault('alert_list', []):
        # Generate alert test registers.
        if 'genautoregs' not in regs and not no_auto_alerts:
            aregs, err = make_alert_regs(regs, offset, addrsep, fullwidth)
            error += err
            autoregs.extend(aregs)
            offset += addrsep * len(aregs)

        num_alerts = 0
        for alert in regs['alert_list']:
            alert_width = int(alert.get('width', '1'), 0)
            num_alerts += alert_width
            if alert_width > 1:
                log.warning(
                    "{}: Consider naming each alert individually instead of "
                    "declaring an alert signal with width > 1.".format(
                        alert['name']))

            # check alert naming scheme
            if alert['name'] == "":
                log.error("{}: Alert name cannot be empty".format(alert['name']))
                error += 1
            prefix = alert['name'].split('_')
            if prefix[0] not in ['recov', 'fatal']:
                log.error(
                    "{}: Alerts must be prefixed with either 'recov_' or "
                    "'fatal_'.".format(alert['name']))
                error += 1

        if num_alerts != 0:
            param = ''
            for p in regs['param_list']:
                if p['name'] == 'NumAlerts':
                    param = p
            if param:
                # We already have an NumAlerts parameter.
                if (param['type'] != 'int' or
                        param['default'] != str(num_alerts) or
                        param['local'] != 'true'):
                    log.error(
                        'Conflicting definition of NumAlerts parameter found.')
                    error += 1
            else:
                # Generate the NumAlerts parameter.
                regs['param_list'].append({
                    'name': 'NumAlerts',
                    'type': 'int',
                    'default': str(num_alerts),
                    'desc': 'Number of alerts',
                    'local': 'true',
                    'expose': 'false',
                })

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

    vld_regs = []
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

            vld_regs.append(x)
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

            vld_regs.append(x)
            continue

        if 'window' in x:
            try:
                window = Window.from_raw(offset, fullwidth,
                                         regs.get('param_list', []),
                                         x['window'])
                vld_regs.append(window)
                offset = window.offset + window.size_in_bytes

                if window.name is not None:
                    if window.name in regs['genrnames']:
                        log.error('Duplicate window name {!r} at offset {:#x}.'
                                  .format(offset, window.name))
                        error += 1
                    regs['genrnames'].append(window.name.lower())
            except ValueError as err:
                log.error('Error in window at offset {:#x}: {}'
                          .format(offset, err))
                error += 1

            continue

        if 'multireg' in x:
            try:
                multi_reg = MultiRegister(offset, addrsep, fullwidth,
                                          regs.get('param_list', []),
                                          x['multireg'])
                vld_regs.append(multi_reg)
                for reg in multi_reg.regs:
                    error += _upd_regnames(regs, offset, reg)
                offset += addrsep * len(multi_reg.regs)
            except ValueError as err:
                log.error('Error in multireg at offset {:#x}: {}'
                          .format(offset, err))
                error += 1
            continue

        try:
            reg = Register.from_raw(fullwidth, offset,
                                    regs.get('param_list', []),
                                    x)
            vld_regs.append(reg)
            error += _upd_regnames(regs, offset, reg)
        except ValueError as err:
            log.error('Error in register at offset {:#x}: {}'
                      .format(offset, err))
            error += 1
        offset += addrsep

    regs['registers'] = vld_regs

    regs['gennextoffset'] = offset
    # make the right thing happen if now exactly on power of 2
    if offset > 0:
        offset -= 1
    regs['gensize'] = 1 << offset.bit_length()

    error += check_wen_regs(regs)

    if autoregs:
        # auto generated registers go at the front
        autoregs.extend(regs['registers'])
        regs['registers'] = autoregs
        regs['genautoregs'] = True

    log.debug("Validated, size = " + hex(regs['gensize']) + " errors=" +
              str(error) + " names are " + str(regs['genrnames']))
    if (error > 0):
        log.error("Register description had " + str(error) + " error" +
                  "s" if error > 1 else "")

    regs.setdefault('inter_signal_list', [])
    regs.setdefault('bus_device', '')
    regs.setdefault('bus_host', '')

    if regs["bus_device"] == "tlul":
        # Add to inter_module_signal
        port_name = "tl" if regs["bus_host"] in ["none", ""] else "tl_d"

        regs["inter_signal_list"].append(
            OrderedDict([('struct', 'tl'), ('package', 'tlul_pkg'),
                         ('type', 'req_rsp'), ('act', 'rsp'),
                         ('name', port_name)]))

    if regs['bus_host'] == "tlul":
        port_name = "tl" if regs["bus_host"] in ["none", ""] else "tl_h"

        regs["inter_signal_list"].append(
            OrderedDict([('struct', 'tl'), ('package', 'tlul_pkg'),
                         ('type', 'req_rsp'), ('act', 'req'),
                         ('name', port_name)]))
    return error
