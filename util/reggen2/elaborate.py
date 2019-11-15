# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Build data structures from Hjson
"""

import logging as log
from typing import List, Optional, Sequence, Tuple
from copy import deepcopy

from .data import *
from .validate import check_int, check_bits


def elab_fields(obj, reg: Reg) -> List[Field]:
    fields = []  # List of fields

    for f in obj:
        field = Field()
        field.name = f["name"]
        field.msb, field.lsb = check_bits(f["bits"], reg.name + " Field")
        fields.append(field)

    return fields


def elab_reg(obj,
             offset: Offset,
             unroll: bool = False,
             params: List[Param] = [],
             prefix: str = "") -> Tuple[Reg, Offset]:
    reg = Reg()
    reg.name = obj["name"]
    reg.offset = deepcopy(offset)  # Use same offset
    assert reg.size.numeric == 4

    # TODO: Software Access

    # TODO: Hardware Access, External, Qualifier, Read Request

    # Elaborating Fields
    reg.fields = elab_fields(obj["fields"], reg)

    # Next offset
    #log.info("New Offset: {} + {}".format(str(reg.offset), str(reg.size)))
    new_offset = reg.offset + reg.size  # Increase 4 Byte
    #log.info("New Offset: {} + {} = {}".format(str(reg.offset), str(reg.size),
    #                                           str(new_offset)))
    return (reg, new_offset)


def elab_multireg(obj, start_offset, unroll, params,
                  prefix) -> Tuple[MultiReg, Offset]:

    offset = deepcopy(start_offset)

    mreg = MultiReg()
    mreg.name = obj["name"]
    mreg.count = obj["count"]
    mreg.offset = offset

    if "fields" in obj:
        # TODO: Implement compact registers
        log.info("MultiReg with fields isn't supported yet")

        # TODO: Calculate the fields size
        # Elaborating Fields
        mreg.fields = elab_fields(obj["fields"], mreg)

    elif "registers" in obj:
        # Loop the registers if "registers" exist

        offset._varnames.append(mreg.name)

        # new_offset is not used, rather, the function calls elab_multireg
        # calculates new offset based on multireg.size
        mregs, new_offset = elab_regs(
            obj=obj["registers"],
            start_offset=offset,
            unroll=unroll,
            params=params,
            prefix=f"{prefix} MultiReg {obj['name']}")
        mreg.regs = mregs

        # Pop current loop
        offset._varnames.pop()

    else:
        log.error(f"MultiReg {obj['name']} doesn't have `fields` "
                  f"nor `registers` in its keys")

    # Register is finalized.

    new_offset = mreg.offset + mreg.size
    # Now, MultiReg size is determined.
    # No further `update_size()` necessary
    mreg.size_calculated = True
    return (mreg, new_offset)


# Elaborate list of registers
def elab_regs(obj,
              start_offset: Optional[Offset] = None,
              unroll: bool = False,
              params: List[Param] = [],
              prefix: str = ""):
    """elaborate multiple registers (hjson obj --> List[Reg])
    """
    regs = []

    if start_offset == None:
        offset = Offset()  # Set num param to 0
    else:
        offset = deepcopy(start_offset)

    skipto = (False, 0)
    for r in obj:
        # process a register
        log.info("Processing Register {}".format(r["name"] if "name" in
                                                 r else "EMPTY"))
        if "skipto" in r:
            # skipto register
            # TODO: Set next registers skipto
            value, error = check_int(r["skipto"], prefix + " Skipto")
            if error:
                log.error("Skip to format is incorrect")
                continue
            skipto = (True, value)
            offset.skipto = skipto
            continue
        elif "window" in r:
            # window register
            log.info("Window isn't supported yet")
            pass
        elif "type" in r and r["type"] == "multireg":
            # TODO: Multi Register
            mreg, new_offset = elab_multireg(obj=r,
                                             start_offset=offset,
                                             unroll=unroll,
                                             params=params,
                                             prefix=prefix)
            regs.append(mreg)
            offset = new_offset
        else:
            # TODO: move below to validate
            if "registers" in obj:
                log.error("Register cannot have a list of registers")
                continue
            reg, new_offset = elab_reg(obj=r,
                                       offset=offset,
                                       unroll=unroll,
                                       params=params,
                                       prefix=prefix)
            regs.append(reg)
            offset = new_offset

        # Clear skipto
        skipto = (False, 0)

    return (regs, offset)


def elab_params(obj, unroll=False, params=[], prefix="") -> List[Param]:
    result = []
    for p in obj:
        # Build Param OBJ
        value = p["default"]

        if not isinstance(value, int) and p["type"] == "int":
            value, error = check_int(value, prefix + " Param " + p["name"])
            if error:
                log.error(f"{p['name']} value ({p['default']}) "
                          f"isn't correct format")
                continue

        if unroll:
            # Check if param exist in given params
            # If not and the type is int and not local, should raise an error
            if p["name"] not in params and p["type"] == "int" and p[
                    "local"] == False:
                log.error(f"Param {p['name']} should have "
                          f"value given if unroll is set")
                continue

            # If the parameter is local, it always uses the register param value
            if p["local"] and p["name"] in params:
                log.warning(f"Param {p['name']} is set to local, "
                            f"ignore given input {params[p['name']]} "
                            f"but use default value {value}")
                continue

            if p["local"] == False and p["name"] in params:
                value = params[p["name"]]

        param = Param(p["name"], value, p["local"])
        result.append(param)

    return result


def elab_sizes(block: Block, regs: List[Reg]):
    """Update offset._var to actual Register Size
    """
    for r in regs:
        r.offset._var = []
        if len(r.offset._varnames) != 0:
            for vn in r.offset._varnames:
                r.offset._var.append(block.get_reg(vn).inner_size)

        if isinstance(r, MultiReg) and len(r.regs) != 0:
            elab_sizes(block, r.regs)


def elaborate(obj=None, unroll=False, params={}) -> Block:
    """

    @param unroll   If the value is True, It uses params dictionary and unroll
                    every registers to have hard-coded offset

    @param params   Dictionary of Paramter List, This shouldn't have `num` key
    """
    if obj == None:
        log.fatal("Cannot process None object!")
        return None

    block = Block()

    # IP Name
    block.name = obj["name"]

    # Parameters
    block.params = []
    if "param_list" in obj:
        block.params = elab_params(obj=obj["param_list"],
                                   unroll=unroll,
                                   params=params,
                                   prefix=block.name)

    # Registers
    #  Assume it has passed the validation process
    block.regs = []
    if "registers" in obj:
        block.regs, new_offset = elab_regs(obj=obj["registers"],
                                           start_offset=None,
                                           unroll=unroll,
                                           params=block.params,
                                           prefix=block.name)

    # 2nd phase
    # after all registers are elaborated, it is time to calculate the _var size
    # Rationale:
    #   The way to add variables of Size is, it adds pointer to MultiReg into
    #   `offset._var` before elaborating the registers in a MultiReg.
    #   That time, the MultiReg doesn't have the actual Size as the registers/
    #   multi-regs under the hood are not calculated.
    #
    #   So, it is quite hard to maintain the live pointer to its parents
    #   MultiReg instances. The pointer should remain but the offset always
    #   deepcopied before entering to its registers. So that the inner size of
    #   MultiReg is calculated incorrectly.
    #
    #   If variable part is not deepcopied, then the _var value keeps changed.
    #   There might be a way only copying the loop pointer not the actual
    #   MultiReg pointers. But I(@eunchan) don't know how to yet.
    #
    #   Eventual solution is, adding the MultiReg names into _varnames first.
    #   Then expanding the Size into _var after all registers are visited.
    #   It creates second path of elaboration but the second path guarantees
    #   all the size of MultiReg are correct.
    elab_sizes(block, block.regs)

    return block
