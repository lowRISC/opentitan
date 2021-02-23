# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated configuration Hjson tree
"""

from .html_helpers import render_td


def genout(outfile, msg):
    outfile.write(msg)


def name_width(x):
    if x.bits.width() == 1:
        return x.name

    return '{}[{}:0]'.format(x.name, x.bits.msb)


# Must have called cfg_validate, so should have no errors


def gen_cfg_html(cfgs, outfile):
    rnames = list(cfgs.regs.name_to_offset.keys())

    genout(outfile, "<p>Referring to the \n")
    genout(
        outfile,
        "<a href=\"https://docs.opentitan.org/doc/rm/comportability_specification\">\n"
    )
    genout(outfile,
           "Comportable guideline for peripheral device functionality</a>,\n")
    genout(outfile,
           "the module <b><code>" + cfgs.name + "</code></b> has \n")
    genout(outfile, "the following hardware interfaces defined.</p>\n")
    # clocks
    genout(
        outfile, "<p><i>Primary Clock:</i> <b><code>" + cfgs.clock_signals[0] +
        "</code></b></p>\n")
    if len(cfgs.clock_signals) > 1:
        genout(outfile, "<p><i>Other Clocks:</i></p>\n")
    else:
        genout(outfile, "<p><i>Other Clocks: none</i></p>\n")
    # bus interfaces
    genout(
        outfile, "<p><i>Bus Device Interface:</i> <b><code>" +
        (cfgs.bus_device or '') + "</code></b></p>\n")
    if cfgs.bus_host is not None:
        genout(
            outfile, "<p><i>Bus Host Interface:</i> <b><code>" +
            cfgs.bus_host + "</code></b></p>\n")
    else:
        genout(outfile, "<p><i>Bus Host Interface: none</i></p>\n")

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
