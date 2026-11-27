# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Helpers for the templates of IPs that are split into a primary and a secondary partition.

The helpers here hold for any split IP and can be shared. Those that cannot be shared live in the
IP's own module, such as manager_split for the clock and reset managers.
"""

from typing import List, TypeVar

T = TypeVar('T')


def check_partition_outputs(items: List[T], ip: str, partition: str, kind: str) -> List[T]:
    """Return `items`, the outputs of one partition of a split IP.

    Raise a ValueError if there are none, since the packed struct of the partition's outputs would
    be empty, which SystemVerilog does not allow. `kind` names the outputs, such as clock or reset.
    """
    if not items:
        raise ValueError(f"the {partition} partition of the {ip} outputs no {kind}, so its "
                         f"output struct would be empty")
    return items
