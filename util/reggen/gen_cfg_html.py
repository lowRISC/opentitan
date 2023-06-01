# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from Block
"""

from typing import TextIO

from reggen.ip_block import IpBlock
from reggen.html_helpers import render_td
from reggen.signal import Signal


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

    comport_url = "https://opentitan.org/book/doc/contributing/hw/comportability"
    genout(outfile,
           '<p>Referring to the <a href="{url}">Comportable guideline for '
           'peripheral device functionality</a>, the module '
           '<b><code>{mod_name}</code></b> has the following hardware '
           'interfaces defined.</p>\n'
           .format(url=comport_url, mod_name=cfgs.name))

    # clocks
    gen_kv(outfile,
           'Primary Clock',
           '<b><code>{}</code></b>'.format(cfgs.clocking.primary.clock))
    other_clocks = cfgs.clocking.other_clocks()
    if other_clocks:
        other_clocks_str = ['<b><code>{}</code></b>'.format(clk)
                            for clk in other_clocks]
        gen_kv(outfile, 'Other Clocks', ', '.join(other_clocks_str))
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

    # Inter-Module Signals
    if not cfgs.inter_signals:
        genout(outfile, "<p><em>Inter-Module Signals: none</em></p>\n")
    else:
        genout(outfile,
               "<p><em>Inter-Module Signals:</em>\n" +
               "<a href=\"/doc/rm/comportability_specification/#inter-signal-handling\">\n" +
               "Reference</a></p>\n")

        genout(outfile,
               "<table class=\"cfgtable\">\n" +
               "  <caption>Inter-Module Signals</caption>\n" +
               "  <thead>\n" +
               "    <tr>\n" +
               "      <th>Port Name</th>\n" +
               "      <th>Package::Struct</th>\n" +
               "      <th>Type</th>\n" +
               "      <th>Act</th>\n" +
               "      <th>Width</th>\n" +
               "      <th>Description</th>\n" +
               "    </tr>\n" +
               "  </thead>\n" +
               "  <tbody>\n")

        for ims in cfgs.inter_signals:
            name = ims.name
            pkg_struct = ims.package + "::" + ims.struct if ims.package is not None else ims.struct
            sig_type = ims.signal_type
            act = ims.act
            width = str(ims.width) if ims.width is not None else "1"
            desc = ims.desc if ims.desc is not None else ""
            genout(outfile,
                   "    <tr>\n" +
                   "      <td>" + name + "</td>\n" +
                   "      <td>" + pkg_struct + "</td>\n" +
                   "      <td>" + sig_type + "</td>\n" +
                   "      <td>" + act + "</td>\n" +
                   "      <td>" + width + "</td>\n" +
                   "      <td>" + desc + "</td>\n" +
                   "    </tr>\n")
            continue

        genout(outfile,
               "  </tbody>\n" +
               "</table>\n")

    if not cfgs.interrupts:
        genout(outfile, "<p><i>Interrupts: none</i></p>\n")
    else:
        genout(outfile, "<p><i>Interrupts:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Interrupt Name</th>" +
            "<th>Type</th><th>Description</th></tr>\n")
        for x in cfgs.interrupts:
            genout(outfile,
                   '<tr><td>{}</td><td>{}</td>{}</tr>'
                   .format(name_width(x),
                           x.intr_type.name,
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

    if not cfgs.countermeasures:
        genout(outfile, "<p><i>Security Countermeasures: none</i></p>\n")
    else:
        genout(outfile, "<p><i>Security Countermeasures:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Countermeasure ID</th>" +
            "<th>Description</th></tr>\n")
        for cm in cfgs.countermeasures:
            genout(outfile,
                   '<tr><td>{}</td>{}</tr>'
                   .format(cfgs.name.upper() + '.' + str(cm),
                           render_td(cm.desc, rnames, None)))
        genout(outfile, "</table>\n")
