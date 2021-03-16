# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated dashboard Hjson tree
"""

import html
import logging as log
import os.path
import re
import sys
from pathlib import Path

import dashboard.dashboard_validate as dashboard_validate
import hjson
import mistletoe as mk

REPO_TOP = Path(__file__).parent.parent.parent.resolve().absolute()


def genout(outfile, msg):
    outfile.write(msg)


STAGE_STRINGS = {
    # Life Stages
    'L0': 'Specification',
    'L1': 'Development',
    'L2': 'Signed Off',
    # Design Stages
    'D0': 'Initial Work',
    'D1': 'Functional',
    'D2': 'Feature Complete',
    'D3': 'Design Complete',
    # Verification Stages
    'V0': 'Initial Work',
    'V1': 'Under Test',
    'V2': 'Testing Complete',
    'V3': 'Verification Complete',
    # DIF Stages (S for Software)
    'S0': 'Initial Work',
    'S1': 'Functional',
    'S2': 'Complete',
    'S3': 'Stable',
}


def convert_stage(stagestr):
    return STAGE_STRINGS.get(stagestr, "UNKNOWN")

def get_doc_url(base, url):
    """ Produce a URL to a document.

    Relative `url`s are relative to `base`, absolute `url`s are relative to the
    repository root.
    """
    assert isinstance(url, str) and len(url) > 0
    if url[0] == '/':
        return url
    else:
        return '/' + base + '/' + url


# Link module name with its design spec doc.
def get_linked_design_spec(obj):
    result = ""
    if 'design_spec' in obj:
        result = "<span title='Design Spec'><a href='{}'>".format(
            get_doc_url(obj['_ip_desc_hjson_dir'], obj['design_spec']))
        result += "<code>{}</code></a></span>".format(html.escape(obj['name']))
    else:
        result = html.escape(obj['name'])

    return result


# Provide the link to the DV plan.
def get_linked_dv_plan(obj):
    if 'dv_doc' in obj:
        return "<span title='DV Document'><a href=\"{}\">DV</a></span>".format(
            get_doc_url(obj['_ip_desc_hjson_dir'], obj['dv_doc']))
    else:
        return ""


# Link the version to the commit id (if available).
def get_linked_version(rev):
    version = html.escape(rev['version'])
    tree = rev['commit_id'] if 'commit_id' in rev else 'master'
    url = "https://github.com/lowrisc/opentitan/tree/{}".format(tree)
    return "<span title='{}'><a href=\"{}\">{}</a></span>".format(
        tree, url, version)


# Link D/V stages with the checklist table.
def get_linked_checklist(obj, rev, stage, is_latest_rev=True):
    if not stage or stage not in rev:
        return ""

    url = ""
    in_page_ref = ""
    if rev[stage] not in ["D0", "V0"]:
        # if in D0 or V0 stage, there is no in-page reference.
        in_page_ref = "#{}".format(html.escape(rev[stage]).lower())

    # If the checklist is available, the commit id is available, and it is not
    # the latest revision, link to the committed version of the checklist.
    # Else, if checklist is available, then link to the current version of the
    # checklist html.
    # Else, link to the template.
    if 'hw_checklist' in obj and 'commit_id' in rev and not is_latest_rev:
        url = "https://github.com/lowrisc/opentitan/tree/{}/{}.md{}".format(
            rev['commit_id'], obj['hw_checklist'], in_page_ref)
    elif 'hw_checklist' in obj:
        url = get_doc_url(obj['_ip_desc_hjson_dir'],
                          obj['hw_checklist'] + in_page_ref)
    else:
        # There is no checklist available, so point to the template.
        # doc/project/hw_checklist.md.tpl is a symlink to ip_checklist.md.tpl,
        # and github doesn't auto-render symlinks, so we have to use the url
        # where the symlink points to.
        url = "https://github.com/lowrisc/opentitan/tree/master/"
        url += "util/uvmdvgen/checklist.md.tpl"

    return "<a href=\"{}\">{}</a>".format(url, html.escape(rev[stage]))


# Link S stages with the checklist table.
def get_linked_sw_checklist(obj, rev, stage, is_latest_rev=True):
    if not stage or stage not in rev:
        return ""

    url = ""
    in_page_ref = ""
    if rev[stage] not in ["S0"]:
        # if in D0 or V0 stage, there is no in-page reference.
        in_page_ref = "#{}".format(html.escape(rev[stage]).lower())

    # If the checklist is available, the commit id is available, and it is not
    # the latest revision, link to the committed version of the checklist.
    # Else, if checklist is available, then link to the current version of the
    # checklist html.
    # Else, link to the template.
    if 'sw_checklist' in obj and 'commit_id' in rev and not is_latest_rev:
        url = "https://github.com/lowrisc/opentitan/tree/{}/{}.md{}".format(
            rev['commit_id'], obj['sw_checklist'], in_page_ref)
    elif 'sw_checklist' in obj:
        url = get_doc_url(obj['_ip_desc_hjson_dir'],
                          obj['sw_checklist'] + in_page_ref)
    else:
        # There is no checklist available, so point to the template.
        url = "https://github.com/lowrisc/opentitan/tree/master/"
        url += "doc/project/sw_checklist.md.tpl"

    return "<a href=\"{}\">{}</a>".format(url, html.escape(rev[stage]))


# Link development stages in "L# : D# : V# : S#" format.
# Hover text over each L, D, V, S indicates the stage mapping.
# D, V, and S stages link to actual checklist items.
def get_development_stage(obj, rev, is_latest_rev=True):
    if "life_stage" not in rev:
        return "&nbsp;"

    life_stage = rev['life_stage']
    life_stage_html = "<span title='{}'>{}</span>".format(
        html.escape(convert_stage(life_stage)), html.escape(life_stage))

    if life_stage != 'L0' and 'design_stage' in rev:
        design_stage = rev['design_stage']
        design_stage_html = "<span title='{}'>{}</span>".format(
            html.escape(convert_stage(design_stage)),
            get_linked_checklist(obj, rev, 'design_stage', is_latest_rev))
    else:
        design_stage_html = "-"

    if life_stage != 'L0' and 'verification_stage' in rev:
        verification_stage = rev['verification_stage']
        verification_stage_html = "<span title='{}'>{}</span>".format(
            html.escape(convert_stage(verification_stage)),
            get_linked_checklist(obj, rev, 'verification_stage',
                                 is_latest_rev))
    else:
        verification_stage_html = "-"

    if life_stage != 'L0' and 'dif_stage' in rev:
        dif_stage = rev['dif_stage']
        dif_stage_html = "<span title='{}'>{}</span>".format(
            html.escape(convert_stage(dif_stage)),
            get_linked_sw_checklist(obj, rev, 'dif_stage', is_latest_rev))
    else:
        dif_stage_html = "-"

    return [
        life_stage_html, design_stage_html, verification_stage_html,
        dif_stage_html
    ]


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

    ip_desc_hjson_dir = hjson_path.parent.relative_to(REPO_TOP)
    obj['_ip_desc_hjson_dir'] = str(ip_desc_hjson_dir)

    # If `revisions` field doesn't exist, the tool assumes the Hjson
    # as the previous project format, which has only one version entry.
    if "revisions" not in obj:
        print_version1_format(obj, outfile)
    else:
        print_multiversion_format(obj, outfile)
        return


# Version 1 (single version) format
def print_version1_format(obj, outfile):
    # yapf: disable
    genout(outfile, "      <tr>\n")
    genout(outfile, "        <td class=\"fixleft\">" +
                    get_linked_design_spec(obj) + "</td>\n")
    genout(outfile, "        <td class=\"dv-plan\">" +
                    get_linked_dv_plan(obj) + "</td>\n")
    genout(outfile, "        <td class=\"version\">" +
                    get_linked_version(obj) + "</td>\n")

    for stage_html in get_development_stage(obj, obj):
        genout(outfile,
               "        <td class=\"hw-stage\">" + stage_html + "</td>\n")

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
    latest_rev = len(revisions) - 1
    outstr = ""
    for i, rev in enumerate(revisions):
        outstr += "      <tr>\n"

        # If only one entry in `revisions`, no need of `rowspan`.
        if len(revisions) == 1:
            outstr += "        <td class='fixleft'>"
            outstr += get_linked_design_spec(obj) + "</td>\n"
            outstr += "        <td class='dv-plan'>"
            outstr += get_linked_dv_plan(obj) + "</td>\n"
        # Print out the module name in the first entry only
        elif i == 0:
            outstr += "        <td class='fixleft' rowspan='{}'>".format(
                len(revisions))
            outstr += get_linked_design_spec(obj) + "</td>\n"
            outstr += "        <td class='hw-stage' rowspan='{}'>".format(
                len(revisions))
            outstr += get_linked_dv_plan(obj) + "</td>\n"

        # Version
        outstr += "        <td class=\"version\">"
        outstr += get_linked_version(rev) + "</td>\n"

        # Development Stage
        for stage_html in get_development_stage(obj, rev, (i == latest_rev)):
            outstr += "        <td class=\"hw-stage\"><span class='hw-stage'>"
            outstr += stage_html
            outstr += "</span></td>\n"

        # Notes
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
        genout(outfile, "        <td class=\"fixleft\"><a href=\"" +
               html.escape(design_spec_html) + "\">" +
               "design spec</a>\n")
    else:
        genout(outfile, "        <td>&nbsp;</td>\n")
    if os.path.exists(dv_plan_md):
        genout(outfile, "        <td class=\"fixleft\"><a href=\"" +
               html.escape(dv_plan_html) + "\">" +
               "DV document</a>\n")
    else:
        genout(outfile, "        <td>&nbsp;</td>\n")

    genout(outfile, "      </tr>\n")
    # yapf: enable
    return
