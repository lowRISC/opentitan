# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from Block
"""

from typing import TextIO

from .ip_block import IpBlock
from .html_helpers import render_td
from .signal import Signal


def genout(outfile: TextIO, msg: str) -> None:
    outfile.write(msg)


def name_width(x: Signal) -> str:
    if x.bits.width() == 1:
        return x.name

    return '{}[{}:0]'.format(x.name, x.bits.msb)


def gen_kv(outfile: TextIO, key: str, value: str) -> None:
    genout(outfile,
           '<p><i>{}:</i> {}</p>\n'.format(key, value))


def gen_cfg_html(cfgs: IpBlock, outfile: TextIO) -> None:
    rnames = cfgs.get_rnames()

    ot_server = 'https://docs.opentitan.org'
    comport_url = ot_server + '/doc/rm/comportability_specification'
    genout(outfile,
           '<p>Referring to the <a href="{url}">Comportable guideline for '
           'peripheral device functionality</a>, the module '
           '<b><code>{mod_name}</code></b> has the following hardware '
           'interfaces defined.</p>\n'
           .format(url=comport_url, mod_name=cfgs.name))

    # clocks
    gen_kv(outfile,
           'Primary Clock',
           '<b><code>{}</code></b>'.format(cfgs.clock_signals[0]))
    if len(cfgs.clock_signals) > 1:
        other_clocks = ['<b><code>{}</code></b>'.format(clk)
                        for clk in cfgs.clock_signals[1:]]
        gen_kv(outfile, 'Other Clocks', ', '.join(other_clocks))
    else:
        gen_kv(outfile, 'Other Clocks', '<i>none</i>')

    # bus interfaces
    dev_ports = ['<b><code>{}</code></b>'.format(port)
                 for port in cfgs.bus_interfaces.get_port_names(False, True)]
    assert dev_ports
    gen_kv(outfile, 'Bus Device Interfaces (TL-UL)', ', '.join(dev_ports))

    host_ports = ['<b><code>{}</code></b>'.format(port)
                  for port in cfgs.bus_interfaces.get_port_names(True, False)]
    if host_ports:
        gen_kv(outfile, 'Bus Host Interfaces (TL-UL)', ', '.join(host_ports))
    else:
        gen_kv(outfile, 'Bus Host Interfaces (TL-UL)', '<i>none</i>')

    # IO
    ios = ([('input', x) for x in cfgs.xputs[1]] +
           [('output', x) for x in cfgs.xputs[2]] +
           [('inout', x) for x in cfgs.xputs[0]])
    if ios:
        genout(outfile, "<p><i>Peripheral Pins for Chip IO:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr>" +
            "<th>Pin name</th><th>direction</th>" +
            "<th>Description</th></tr>\n")
        for direction, x in ios:
            genout(outfile,
                   '<tr><td>{}</td><td>{}</td>{}</tr>'
                   .format(name_width(x),
                           direction,
                           render_td(x.desc, rnames, None)))
        genout(outfile, "</table>\n")
    else:
        genout(outfile, "<p><i>Peripheral Pins for Chip IO: none</i></p>\n")

    if not cfgs.interrupts:
        genout(outfile, "<p><i>Interrupts: none</i></p>\n")
    else:
        genout(outfile, "<p><i>Interrupts:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Interrupt Name</th>" +
            "<th>Description</th></tr>\n")
        for x in cfgs.interrupts:
            genout(outfile,
                   '<tr><td>{}</td>{}</tr>'
                   .format(name_width(x),
                           render_td(x.desc, rnames, None)))
        genout(outfile, "</table>\n")

    if not cfgs.alerts:
        genout(outfile, "<p><i>Security Alerts: none</i></p>\n")
    else:
        genout(outfile, "<p><i>Security Alerts:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Alert Name</th>" +
            "<th>Description</th></tr>\n")
        for x in cfgs.alerts:
            genout(outfile,
                   '<tr><td>{}</td>{}</tr>'
                   .format(x.name,
                           render_td(x.desc, rnames, None)))
        genout(outfile, "</table>\n")
