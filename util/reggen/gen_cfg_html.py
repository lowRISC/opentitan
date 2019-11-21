# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated configuration Hjson tree
"""

import sys


def genout(outfile, msg):
    outfile.write(msg)


def name_width(x):
    if not 'width' in x or x['width'] == '1':
        return x['name']
    return x['name'] + '[' + str(int(x['width'], 0) - 1) + ':0]'


# Must have called cfg_validate, so should have no errors


def gen_cfg_html(cfgs, outfile):
    genout(outfile, "<p>Referring to the \n")
    genout(
        outfile,
        "<a href=\"https://docs.opentitan.org/doc/rm/comportability_specification\">\n"
    )
    genout(outfile, "Comportable guideline for peripheral device functionality</a>,\n")
    genout(outfile,
           "the module <b><code>" + cfgs['name'] + "</code></b> has \n")
    genout(outfile, "the following hardware interfaces defined.</p>\n")
    # clocks
    genout(
        outfile, "<p><i>Primary Clock:</i> <b><code>" + cfgs['clock_primary'] +
        "</code></b></p>\n")
    if 'other_clock_list' in cfgs:
        genout(outfile, "<p><i>Other Clocks:</i></p>\n")
    else:
        genout(outfile, "<p><i>Other Clocks: none</i></p>\n")
    # bus interfaces
    genout(
        outfile, "<p><i>Bus Device Interface:</i> <b><code>" +
        cfgs['bus_device'] + "</code></b></p>\n")
    if 'bus_host' in cfgs:
        genout(
            outfile, "<p><i>Bus Host Interface:</i> <b><code>" +
            cfgs['bus_host'] + "</code></b></p>\n")
    else:
        genout(outfile, "<p><i>Bus Host Interface: none</i></p>\n")
    # IO
    if ('available_input_list' in cfgs or 'available_output_list' in cfgs or
            'available_inout_list' in cfgs):
        genout(outfile, "<p><i>Peripheral Pins for Chip IO:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr>" +
            "<th>Pin name</th><th>direction</th>" +
            "<th>Description</th></tr>\n")
        if 'available_input_list' in cfgs:
            for x in cfgs['available_input_list']:
                genout(
                    outfile, "<tr><td>" + name_width(x) +
                    "</td><td>input</td><td>" + x['desc'] + "</td></tr>\n")
        if 'available_output_list' in cfgs:
            for x in cfgs['available_output_list']:
                genout(
                    outfile, "<tr><td>" + name_width(x) +
                    "</td><td>output</td><td>" + x['desc'] + "</td></tr>\n")
        if 'available_inout_list' in cfgs:
            for x in cfgs['available_inout_list']:
                genout(
                    outfile, "<tr><td>" + name_width(x) +
                    "</td><td>inout</td><td>" + x['desc'] + "</td></tr>\n")
        genout(outfile, "</table>\n")
    else:
        genout(outfile, "<p><i>Peripheral Pins for Chip IO: none</i></p>\n")
    # interrupts
    if 'interrupt_list' in cfgs:
        genout(outfile, "<p><i>Interrupts:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Interrupt Name</th>" +
            "<th>Description</th></tr>\n")
        for x in cfgs['interrupt_list']:
            genout(
                outfile, "<tr><td>" + name_width(x) + "</td><td>" + x['desc'] +
                "</td></tr>\n")
        genout(outfile, "</table>\n")
    else:
        genout(outfile, "<p><i>Interrupts: none</i></p>\n")
    if 'alert_list' in cfgs:
        genout(outfile, "<p><i>Security Alerts:</i></p>\n")
        genout(
            outfile, "<table class=\"cfgtable\"><tr><th>Alert Name</th>" +
            "<th>Description</th></tr>\n")
        for x in cfgs['alert_list']:
            genout(
                outfile, "<tr><td>" + x['name'] + "</td><td>" + x['desc'] +
                "</td></tr>\n")
        genout(outfile, "</table>\n")
    else:
        genout(outfile, "<p><i>Security Alerts: none</i></p>\n")
    # interrupts
    return
