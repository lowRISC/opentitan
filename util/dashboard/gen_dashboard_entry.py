# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated dashboard Hjson tree
"""

import sys
import hjson
import html
import re
import dashboard.dashboard_validate as dashboard_validate
import logging as log
import os.path
import mistletoe as mk


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

    # If `revisions` field doesn't exist, the tool assumes the Hjson
    # as the previous project format, which has only one version entry.
    if not "revisions" in obj:
        print_version1_format(obj, outfile)
    else:
        print_multiversion_format(obj, outfile)
        return


# Version 1 (single version) format
def print_version1_format(obj, outfile):
    life_stage = obj['life_stage']
    life_stage_mapping = convert_stage(obj['life_stage'])

    # yapf: disable
    genout(outfile, "      <tr>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    html.escape(obj['name']) + "</td>\n")
    genout(outfile, "        <td class=\"hw-stage\">" +
                    html.escape(obj['version']) + "</td>\n")
    genout(outfile, "        <td class=\"hw-stage\"><span class='hw-stage' title='" +
                    html.escape(life_stage_mapping) + "'>" +
                    html.escape(life_stage) + "</span></td>\n")
    if life_stage != 'L0' and 'design_stage' in obj:
        design_stage_mapping = convert_stage(obj['design_stage'])
        genout(outfile,
                    "        <td class=\"hw-stage\"><span class='hw-stage' title='" +
                    html.escape(design_stage_mapping) + "'>" +
                    html.escape(obj['design_stage']) + "</span></td>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")
    if life_stage != 'L0' and 'verification_stage' in obj:
        verification_stage_mapping = convert_stage(obj['verification_stage'])
        genout(outfile,
                    "        <td class=\"hw-stage\"><span class='hw-stage' title='" +
                    html.escape(verification_stage_mapping) + "'>" +
                    html.escape(obj['verification_stage']) + "</span></td>\n")
    else:
        genout(outfile,
                    "        <td>&nbsp;</td>\n")

    # Empty commit ID
    genout(outfile, "        <td>&nbsp;</td>\n")

    if 'notes' in obj:
        genout(outfile,
                    "        <td>" + mk.markdown(obj['notes']).rstrip() + "</td>\n")
    else:
        genout(outfile,
                    "        <td><p>&nbsp;</p></td>\n")
    genout(outfile, "      </tr>\n")
    # yapf: enable


def print_multiversion_format(obj, outfile):
    # Sort the revision list based on the version field.
    # TODO: If minor version goes up gte than 10?
    revisions = sorted(obj["revisions"], key=lambda x: x["version"])
    outstr = ""
    for i, rev in enumerate(revisions):
        outstr += "      <tr>\n"

        # If only one entry in `revisions`, no need of `rowspan`.
        if len(revisions) == 1:
            outstr += "        <td class='fixleft'>"
            outstr += html.escape(obj['name']) + "</td>\n"
        # Print out the module name in the first entry only
        elif i == 0:
            outstr += "        <td class='fixleft' rowspan='{}'>".format(
                len(revisions))
            outstr += html.escape(obj['name']) + "</td>\n"

        # Version
        outstr += "        <td class=\"hw-stage\">"
        outstr += html.escape(rev['version']) + "</td>\n"

        # Life Stage
        life_stage = rev['life_stage']
        life_stage_mapping = convert_stage(rev['life_stage'])

        outstr += "        <td class=\"hw-stage\"><span class='hw-stage' title='"
        outstr += html.escape(life_stage_mapping) + "'>"
        outstr += html.escape(life_stage) + "</span></td>\n"

        if life_stage != 'L0' and 'design_stage' in rev:
            design_stage_mapping = convert_stage(rev['design_stage'])
            outstr += "        <td class=\"hw-stage\"><span class='hw-stage' title='"
            outstr += html.escape(design_stage_mapping) + "'>"
            outstr += html.escape(rev['design_stage']) + "</span></td>\n"
        else:
            outstr += "        <td>&nbsp;</td>\n"

        if life_stage != 'L0' and 'verification_stage' in rev:
            verification_stage_mapping = convert_stage(
                rev['verification_stage'])
            outstr += "        <td class=\"hw-stage\"><span class='hw-stage' title='"
            outstr += html.escape(verification_stage_mapping) + "'>"
            outstr += html.escape(rev['verification_stage']) + "</span></td>\n"
        else:
            outstr += "        <td>&nbsp;</td>\n"

        if 'commit_id' in rev:
            outstr += "        <td class=\"hw-stage\">"
            outstr += "<a href='https://github.com/lowrisc/opentitan/tree/{}'>{}</a>".format(
                rev['commit_id'], rev['commit_id'][0:7])
            outstr += "</td>\n"
        else:
            outstr += "        <td>&nbsp;</td>\n"

        if 'notes' in rev and rev['notes'] != '':
            outstr += "        <td>" + mk.markdown(
                rev['notes']).rstrip() + "</td>\n"
        else:
            outstr += "        <td><p>&nbsp;</p></td>\n"
        outstr += "      </tr>\n"

    genout(outfile, outstr)


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
        log.error("hjson file import failed")

    # create design spec and DV plan references, check for existence below
    design_spec_md = re.sub(r'/data/', '/doc/',
                            re.sub(r'\.prj\.hjson', '.md', str(hjson_path)))
    dv_plan_md = re.sub(
        r'/data/', '/doc/',
        re.sub(r'\.prj\.hjson', '_dv_plan.md', str(hjson_path)))
    design_spec_html = re.sub(
        r'/data/', '/doc/',
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
