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

    # Software Access

    # Hardware Access

    # Elaborating Fields
    reg.fields = elab_fields(obj["fields"], reg)

    # Next offset
    log.info("New Offset: {} + {}".format(str(reg.offset), str(reg.size)))
    new_offset = reg.offset + reg.size  # Increase 4 Byte
    log.info("New Offset: {} + {} = {}".format(str(reg.offset), str(reg.size),
                                               str(new_offset)))
    return (reg, new_offset)


def elab_regs(obj,
              start_offset: Optional[Offset] = None,
              unroll: bool = False,
              params: List[Param] = [],
              prefix: str = ""):
    regs = []

    if start_offset == None:
        offset = Offset({"num": 0})  # Set num param to 0
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

            if "fields" in r:
                # TODO: Implement compact registers
                log.info("MultiReg with fields isn't supported yet")

                # TODO: Calculate the fields size
                # Elaborating Fields
                mreg = MultiReg()
                mreg.name = r["name"]
                mreg.count = r["count"]
                mreg.fields = elab_fields(r["fields"], mreg)
                regs.append(mreg)

                # TODO: Add "div" field

                offset += mreg.size

                pass
            elif "registers" in r:
                # Loop the registers if "registers" exist
                mregs, new_offset = elab_regs(obj=r["registers"],
                                              start_offset=offset,
                                              unroll=unroll,
                                              params=params,
                                              prefix=prefix +
                                              " MultiReg {}".format(r["name"]))

                mreg = MultiReg()
                mreg.name = r["name"]
                mreg.count = r["count"]
                mreg.regs = mregs
                mreg.offset = deepcopy(offset)
                regs.append(mreg)

                # Adding parameter
                if r["count"] in offset.params:
                    offset.params[r["count"]] += mreg.inner_size
                else:
                    offset.params[r["count"]] = mreg.inner_size

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
                log.error("{} value ({}) isn't correct format".format(
                    p["name"], p["default"]))
                continue

        if unroll:
            # Check if param exist in given params
            # If not and the type is int and not local, should raise an error
            if p["name"] not in params and p["type"] == "int" and p[
                    "local"] == False:
                log.error(
                    "Param {} should have value given if unroll is set".format(
                        p["name"]))
                continue

            # If the parameter is local, it always uses the register param value
            if p["local"] and p["name"] in params:
                log.warning(
                    "Param {} is set to local, ignore given input {} but use default value {}"
                    .format(p["name"], params[p["name"]], value))
                continue

            if p["local"] == False and p["name"] in params:
                value = params[p["name"]]

        param = Param(p["name"], value, p["local"])
        result.append(param)

    return result


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
    block.name = obj["name"].lower()

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

    return block
