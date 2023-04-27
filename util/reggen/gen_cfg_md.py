# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate markdown documentation for the interfaces of an IpBlock."""

from typing import TextIO, List, Tuple

from reggen.ip_block import IpBlock
from reggen.md_helpers import (
    title, url, italic, coderef, regref_to_link, name_width, table, list_item,
)


def gen_cfg_md(cfgs: IpBlock, output: TextIO) -> None:
    comport_url = url(
        "Comportable guideline for peripheral device functionality",
        "https://opentitan.org/book/doc/rm/comportability_specification",
    )
    output.write(
        f'Referring to the {comport_url}, the module '
        f'{coderef(cfgs.name)} has the following hardware interfaces defined\n',
    )

    list_items: List[str] = []
    tables: List[Tuple[
        str,
        List[str],
        List[List[str]],
    ]] = []

    # Clocks
    primary_clock = cfgs.clocking.primary.clock
    assert primary_clock
    list_items.append('Primary Clock: ' + coderef(primary_clock))

    other_clocks = cfgs.clocking.other_clocks()
    list_items.append(
        "Other Clocks: " +
        (", ".join(coderef(clk) for clk in other_clocks) if other_clocks else italic("none"))
    )

    # Bus Interfaces
    dev_ports = [coderef(port) for port in cfgs.bus_interfaces.get_port_names(False, True)]
    assert dev_ports
    list_items.append("Bus Device Interfaces (TL-UL): " + ", ".join(dev_ports))

    host_ports = [coderef(port) for port in cfgs.bus_interfaces.get_port_names(True, False)]
    list_items.append(
        "Bus Host Interfaces (TL-UL): " +
        (", ".join(host_ports) if host_ports else italic("none"))
    )

    # IO
    ios = ([('input', x) for x in cfgs.xputs[1]] +
           [('output', x) for x in cfgs.xputs[2]] +
           [('inout', x) for x in cfgs.xputs[0]])

    if not ios:
        list_items.append("Peripheral Pins for Chip IO: " + italic("none"))
    else:
        rows = [
            [name_width(x), direction, regref_to_link(x.desc)]
            for direction, x in ios
        ]
        tables.append((
            "Peripheral Pins for Chip IO",
            ["Pin name", "Direction", "Description"],
            rows,
        ))

    # Inter-Module Signals
    if not cfgs.inter_signals:
        list_items.append("Inter-Module Signals: " + italic("none"))
    else:
        rows = []
        for ims in cfgs.inter_signals:
            name = ims.name
            pkg_struct = ims.package + "::" + ims.struct if ims.package is not None else ims.struct
            sig_type = ims.signal_type
            act = ims.act
            width = str(ims.width) if ims.width is not None else "1"
            desc = ims.desc if ims.desc is not None else ""
            rows.append([name, pkg_struct, sig_type, act, width, desc])

        comportibility_url = (
            "https://opentitan.org/book/doc/contributing/hw/comportability/index.html"
            "#inter-signal-handling"
        )
        tables.append((
            url("Inter-Module Signals", comportibility_url),
            ["Port Name", "Package::Struct", "Type", "Act", "Width", "Description"],
            rows,
        ))

    # Interrupts
    if not cfgs.interrupts:
        list_items.append("Interrupts: " + italic("none"))
    else:
        rows = [
            [name_width(x), x.intr_type.name, regref_to_link(x.desc)]
            for x in cfgs.interrupts
        ]
        tables.append((
            "Interrupts",
            ["Interrupt Name", "Type", "Description"],
            rows,
        ))

    # Alerts
    if not cfgs.alerts:
        list_items.append("Security Alerts: " + italic("none"))
    else:
        rows = [
            [x.name, regref_to_link(x.desc)]
            for x in cfgs.alerts
        ]
        tables.append((
            "Security Alerts",
            ["Alert Name", "Description"],
            rows,
        ))

    # Countermeasures
    if not cfgs.countermeasures:
        list_items.append("Security Countermeasures: " + italic("none"))
    else:
        rows = [
            [cfgs.name.upper() + '.' + str(cm), regref_to_link(cm.desc)]
            for cm in cfgs.countermeasures
        ]
        tables.append((
            "Security Countermeasures",
            ["Countermeasure ID", "Description"],
            rows,
        ))

    for item in list_items:
        output.write(list_item(item))

    output.write("\n")

    for (table_title, header, rows) in tables:
        output.write(title(table_title, 2) + table(header, rows))
