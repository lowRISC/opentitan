# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate html documentation from validated dashboard json tree
"""

import hjson
import html
import re
import dashboard.dashboard_validate as dashboard_validate
import logging as log
import os.path


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


# Create dashboard of hardware IP development status
def gen_dashboard_html(hjson_path, outfile):
    with hjson_path:
        prjfile = open(str(hjson_path))
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


# Create table of hardware specifications
def gen_specboard_html(hjson_path, rel_hjson_path, outfile):
    with hjson_path:
        prjfile = open(str(hjson_path))
        try:
            obj = hjson.load(prjfile)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])
    if dashboard_validate.validate(obj) == 0:
        log.info("Generated dashboard object for " + str(hjson_path))
    else:
        log.fail("hjson file import failed")

    # create design spec and DV plan references, check for existence below
    design_spec_md = re.sub(r'/data/', '/doc/',
                            re.sub(r'\.prj\.hjson', '.md', str(hjson_path)))
    dv_plan_md = re.sub(
        r'/data/', '/doc/',
        re.sub(r'\.prj\.hjson', '_dv_plan.md', str(hjson_path)))
    design_spec_html = re.sub(r'/data/', '/doc/',
        re.sub(r'\.prj\.hjson', '.html', str(rel_hjson_path)))
    dv_plan_html = re.sub(
        r'/data/', '/doc/',
        re.sub(r'\.prj\.hjson', '_dv_plan.html', str(rel_hjson_path)))

    # yapf: disable
    genout(outfile, "      <tr>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    html.escape(obj['name']) + "</td>\n")
    if os.path.exists(design_spec_md):
        genout(outfile,
                    "        <td class=\"fixleft\"><a href=\"" +
                    html.escape(design_spec_html) + "\">" +
                    "design spec</a>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    if os.path.exists(dv_plan_md):
        genout(outfile,
                    "        <td class=\"fixleft\"><a href=\"" +
                    html.escape(dv_plan_html) + "\">" +
                    "DV plan</a>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    genout(outfile, "      </tr>\n")
    # yapf: enable
    return
