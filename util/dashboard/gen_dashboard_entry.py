# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate html documentation from validated dashboard json tree
"""

import hjson
import html
import dashboard.dashboard_validate as dashboard_validate
import logging as log


def genout(outfile, msg):
    outfile.write(msg)


STAGE_STRINGS = {
    'L0': 'Specification',
    'L1': 'Development',
    'L2': 'Signed Off',
    'D0': 'Initial Work',
    'D1': 'Functional',
    'D2': 'Feature Complete',
    'D3': 'Design Complete',
    'V0': 'Initial Work',
    'V1': 'Under Test',
    'V2': 'Testing Complete',
    'V3': 'Verification Complete'
}


def convert_stage(stagestr):
    return STAGE_STRINGS.get(stagestr, "UNKNOWN")


def gen_html(hjson_path, outfile):
    with hjson_path:
        prjfile = open(hjson_path)
        try:
            obj = hjson.load(prjfile)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])
    if dashboard_validate.validate(obj) == 0:
        log.info("Generated dashboard object for " + str(hjson_path))
    else:
        log.fail("hjson file import failed\n")

    life_stage = obj['life_stage']
    life_stage_mapping = convert_stage(obj['life_stage'])

    # yapf: disable
    genout(outfile, "      <tr>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    html.escape(obj['name']) + "</td>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    html.escape(obj['version']) + "</td>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    html.escape(life_stage) + " - " +
                    html.escape(life_stage_mapping) + "</td>\n")
    if life_stage != 'L0' and 'design_stage' in obj:
        design_stage_mapping = convert_stage(obj['design_stage'])
        genout(outfile,
                    "        <td class=\"fixleft\">" +
                    html.escape(obj['design_stage']) + " - " +
                    html.escape(design_stage_mapping) + "</td>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    if life_stage != 'L0' and 'verification_stage' in obj:
        verification_stage_mapping = convert_stage(obj['verification_stage'])
        genout(outfile,
                    "        <td class=\"fixleft\">" +
                    html.escape(obj['verification_stage']) + " - " +
                    html.escape(verification_stage_mapping) + "</td>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    if 'notes' in obj:
        genout(outfile,
                    "        <td>" + html.escape(obj['notes']) + "</td>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    genout(outfile, "      </tr>\n")
    # yapf: enable
    return
