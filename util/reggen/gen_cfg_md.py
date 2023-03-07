# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate Markdown documentation from Block
"""

from typing import TextIO

from reggen.ip_block import IpBlock
from reggen.md_helpers import url, italic, coderef, render_td, name_width, table


def genout(outfile: TextIO, msg: str) -> None:
    outfile.write(msg)

def gen_kv(outfile: TextIO, key: str, value: str) -> None:
    genout(outfile, f'- {italic(key)}: {value}\n')

def gen_cfg_md(cfgs: IpBlock, outfile: TextIO) -> None:
    rnames = cfgs.get_rnames()

    ot_server = 'https://docs.opentitan.org'
    comport_url = ot_server + '/doc/rm/comportability_specification'
    comport_url = url("Comportable guideline for peripheral device functionality", comport_url)
    genout(outfile,
           f'Referring to the {comport_url}, the module '
           f'{coderef(cfgs.name)} has the following hardware '
           'interfaces defined\n')

    # clocks
    gen_kv(outfile,
           'Primary Clock',
           coderef(cfgs.clocking.primary.clock))
    other_clocks = cfgs.clocking.other_clocks()
    if other_clocks:
        other_clocks_str = [coderef(clk) for clk in other_clocks]
        gen_kv(outfile, 'Other Clocks', ', '.join(other_clocks_str))
    else:
        gen_kv(outfile, 'Other Clocks', italic("none"))

    # bus interfaces
    dev_ports = [coderef(port) for port in cfgs.bus_interfaces.get_port_names(False, True)]
    assert dev_ports
    gen_kv(outfile, 'Bus Device Interfaces (TL-UL)', ', '.join(dev_ports))

    host_ports = [coderef(port) for port in cfgs.bus_interfaces.get_port_names(True, False)]
    if host_ports:
        gen_kv(outfile, 'Bus Host Interfaces (TL-UL)', ', '.join(host_ports))
    else:
        gen_kv(outfile, 'Bus Host Interfaces (TL-UL)', italic("none"))

    # IO
    ios = ([('input', x) for x in cfgs.xputs[1]] +
           [('output', x) for x in cfgs.xputs[2]] +
           [('inout', x) for x in cfgs.xputs[0]])
    if ios:
        gen_kv(outfile, "Peripheral Pins for Chip IO", "")
        header = ["Pin name", "Direction", "Description"]
        rows = []
        for direction, x in ios:
            rows.append([name_width(x), direction, render_td(x.desc, rnames)])
        genout(outfile, "\n")
        genout(outfile, table(header, rows))
        genout(outfile, "\n")
    else:
        gen_kv(outfile, "Peripheral Pins for Chip IO", italic("none"))

    # Inter-Module Signals
    if not cfgs.inter_signals:
        gen_kv(outfile, "Inter-Module Signals", italic("none"))
    else:
        gen_kv(outfile, "Inter-Module Signals",
               url("Reference", "/doc/rm/comportability_specification/#inter-signal-handling"))
        header = ["Port Name", "Package::Struct", "Type", "Act", "Width", "Description"]
        rows = []
        for ims in cfgs.inter_signals:
            name = ims.name
            pkg_struct = ims.package + "::" + ims.struct if ims.package is not None else ims.struct
            sig_type = ims.signal_type
            act = ims.act
            width = str(ims.width) if ims.width is not None else "1"
            desc = ims.desc if ims.desc is not None else ""
            rows.append([name, pkg_struct, sig_type, act, width, desc])
        genout(outfile, "\n")
        genout(outfile, table(header, rows))
        genout(outfile, "\n")

    # Interrupts
    if not cfgs.interrupts:
        gen_kv(outfile, "Interrupts", italic("none"))
    else:
        gen_kv(outfile, "Interrupts", "")
        header = ["Interrupt Name", "Type", "Description"]
        rows = []
        for x in cfgs.interrupts:
            rows.append([name_width(x), x.intr_type.name, render_td(x.desc, rnames)])
        genout(outfile, "\n")
        genout(outfile, table(header, rows))
        genout(outfile, "\n")

    # Alerts
    if not cfgs.alerts:
        gen_kv(outfile, "Security Alerts", italic("none"))
    else:
        gen_kv(outfile, "Security Alerts", "")
        header = ["Alert Name", "Description"]
        rows = []
        for x in cfgs.alerts:
            rows.append([x.name, render_td(x.desc, rnames)])
        genout(outfile, "\n")
        genout(outfile, table(header, rows))
        genout(outfile, "\n")

    # countermeasures
    if not cfgs.countermeasures:
        gen_kv(outfile, "Security Countermeasures", italic("none"))
    else:
        gen_kv(outfile, "Security Countermeasures", "")
        header = ["Countermeasure ID", "Description"]
        rows = []
        for cm in cfgs.countermeasures:
            rows.append([cfgs.name.upper() + '.' + str(cm), render_td(cm.desc, rnames)])
        genout(outfile, "\n")
        genout(outfile, table(header, rows))
        genout(outfile, "\n")
