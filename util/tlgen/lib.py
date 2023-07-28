# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from typing import Any, Dict, List, Optional, Tuple, Union


def is_pow2(v: Any) -> bool:
    """Return true if value is power of two
    """
    if not isinstance(v, int):
        log.warning("is_pow2 received non-integer value {}".format(v))
        return False
    return (v > 0) and (v & (v - 1) == 0)


def simplify_addr(dev: Dict[Any, Any],
                  xbar: Dict[Any, Any]) -> List[Dict[Any, Any]]:
    """Make smaller entries by combining them

    If any contiguous regions exist, concatenate them.
    For instance, 0x1000 ~ 0x1FFF , 0x2000~ 0x2FFF ==> 0x1000 ~ 0x2FFF

    It also checks if there's no device between the gap, then merge
    the ranges. For instance:

    {0x4000_0000, 0x1_0000}, {0x4008_0000, 0x1_0000} then it combines two
    entries into {0x4000_0000, 0x9_0000}

    @param addrs List of Dict[Addr] : {'base_addr':,'size_byte':}
    """

    addrs = dev["addr_range"]
    # Sort based on the base addr
    newlist = sorted(addrs, key=lambda k: int(k['base_addr'], 0))
    # check if overlap or contiguous
    result: List[Dict[Any, Any]] = []
    for e in newlist:
        if len(result) == 0:
            result.append(e)
            continue
        # if contiguous
        if int(e["base_addr"], 0) == int(result[-1]["base_addr"], 0) + int(
                result[-1]["size_byte"], 0):
            # update previous entry size
            result[-1]["size_byte"] = "0x{:x}".format(
                int(result[-1]["size_byte"], 0) + int(e["size_byte"], 0))
            continue

        if no_device_in_range(xbar, dev["name"], result[-1], e):
            # Determine if size can be power of 2 value
            next_value = (get_next_base_addr(e["base_addr"], xbar,
                                             dev["name"]) or
                          0x100000000)

            calc_size = int(e["base_addr"], 0) + int(e["size_byte"], 0) - int(
                result[-1]["base_addr"], 0)

            # find power of 2 if possible
            size_byte = find_pow2_size(result[-1], calc_size, next_value)

            result[-1]["size_byte"] = "0x{:x}".format(size_byte)
            continue

        # If overlapping (Should it be consider? TlGen will catch it)

        # Normal case
        result.append(e)

    # return result
    return result


def no_device_in_range(xbar: Dict[Any, Any],
                       name: str,
                       f: Dict[Any, Any],
                       t: Dict[Any, Any]) -> bool:
    """Check if other devices doesn't overlap with the range 'from <= x < to'
    """
    from_addr = int(f["base_addr"], 0) + int(f["size_byte"], 0)
    to_addr = int(t["base_addr"], 0)

    for node in [
            x for x in xbar["nodes"]
            if x["type"] == "device" and not x["name"] == name
    ]:
        if "addr_range" not in node:
            # Xbar?
            log.info("Xbar type node cannot be compared in this version.",
                     "Please use in caution")
            continue
        assert isinstance(node["addr_range"], list)

        for addr in node["addr_range"]:
            b_addr = int(addr["base_addr"], 0)
            e_addr = b_addr + int(addr["size_byte"], 0)

            if e_addr <= from_addr or b_addr >= to_addr:
                # No overlap
                continue
            return False
    return True


def get_next_base_addr(addr: Union[str, int],
                       xbar: Dict[Any, Any],
                       name: str) -> Optional[int]:
    """Return the least value of base_addr of the IP greater than addr

    """
    if isinstance(addr, str):
        value = int(addr, 0)
    else:
        assert isinstance(addr, int)
        value = addr

    device_list = [
        x for x in xbar["nodes"]
        if x["type"] == "device" and not x["name"] == name
    ]

    try:
        addrs = [a for r in device_list for a in r["addr_range"]]
    except KeyError:
        log.error("Address range is wrong.\n {}".format(
            [x for x in device_list if "addr_range" not in x]))
        raise SystemExit()

    sorted_list = sorted(addrs, key=lambda k: int(k["base_addr"], 0))

    gte_list = [x for x in sorted_list if int(x["base_addr"], 0) > value]

    if len(gte_list) == 0:
        return None

    return int(gte_list[0]["base_addr"], 0)


def find_pow2_size(addr: Dict[Any, Any],
                   min_size: int,
                   next_value: int) -> int:
    """Find smallest power of 2 value greater than min_size by given addr.

    For instance, {addr:0x4000_0000, min_size:0x21000} and `next_value` as
    0x40080000, the result will be 0x4_0000

    But it should return result not exceeding the base_addr's leading one bit
    position. For instance, if the base_addr is 0x4003_0000, the return value
    should be less than or equal to 0x1_0000. Cannot be 0x4_0000. So, this
    case, the function returns the original min_size value 0x21000.
    """
    base_addr = int(addr["base_addr"], 0)

    diff = next_value - base_addr

    # Find the least one bit position.
    # If base_addr is 0, then any value can be used
    if not base_addr == 0:
        leading_one = 1
        while True:
            if base_addr & leading_one != 0:
                break
            leading_one = leading_one << 1

        if leading_one <= diff:
            diff = leading_one

    i = 1
    while True:
        i = i << 1
        if i >= min_size:
            break

    # If found pow2 value is greater than diff, it cannot be used. Just use
    # min_size then the tool will use comparators (>=, <=)
    if i > diff:
        i = min_size

    # Minimum size is one 32bit register.
    assert i >= 0x4

    return i


def get_toggle_excl_bits(addr_ranges: List[List[int]],
                         addr_width: int = 32) -> List[Tuple[int, int]]:
    """ Input addr_ranges is a list of (start_addr, end_addr)
    From given addr_ranges, will calculate what address bits can't be toggled as
    only the address in the ranges can pass through the xbar to the device
    """
    excl_bits = []  # list of (start_bit, end_bit)

    # Find all the bits that can be toggled to 1
    toggle_bits = 0
    for addr in addr_ranges:
        # The size of the addres range should be power of 2
        assert is_pow2(addr[1] - addr[0] + 1)

        toggle_bits |= addr[0]
        toggle_bits |= addr[1] - addr[0]

    # Assume toggle_bits = 010011, generate below as bit 2, 3, 5 are never toggled
    # excl_bits = [(5,5), (2,3)]
    start_bit = -1
    for i in range(addr_width):
        bit = toggle_bits & 1
        if not bit and start_bit == -1:
            start_bit = i
        elif bit and start_bit != -1:
            excl_bits.append((start_bit, i - 1))
            start_bit = -1

        toggle_bits = toggle_bits >> 1

    # Handle tailing zero, which are also never toggled
    if start_bit != -1:
        excl_bits.append((start_bit, addr_width - 1))

    return excl_bits
