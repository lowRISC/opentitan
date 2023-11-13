# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation from validated dashboard Hjson tree
"""

import html
import logging as log
import sys
from pathlib import Path
from typing import TextIO, Tuple, Union

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
    'D2S': 'Security Countermeasures Complete',
    'D3': 'Design Complete',
    # Verification Stages
    'V0': 'Initial Work',
    'V1': 'Under Test',
    'V2': 'Testing Complete',
    'V2S': 'Testing Complete, With Security Countermeasures Verified',
    'V3': 'Verification Complete',
    # DIF Stages (S for Software)
    'S0': 'Initial Work',
    'S1': 'Functional',
    'S2': 'Complete',
    'S3': 'Stable',
    # In case certain development stages do not apply
    # (e.g. verification handled at the top-level).
    'N/A': 'Not Applicable'
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
        return '/book' + url
    else:
        return '/book/' + base + '/' + url


# Link module name with its design spec doc.
def get_linked_design_spec(obj):
    result = ""
    if 'design_spec' in obj:
        design_spec_url = get_doc_url(
            obj['_ip_desc_hjson_dir'], obj['design_spec']) + "/.."
        result = f"<span title='Design Spec'><a href='{design_spec_url}'>"
        result += f"<code>{html.escape(obj['name'])}</code></a></span>"
    else:
        result = html.escape(obj['name'])

    return result


# Provide the link to the DV document.
def get_linked_dv_doc(obj):
    if 'dv_doc' in obj:
        url = (get_doc_url(obj['_ip_desc_hjson_dir'], obj['dv_doc']) +
               "/../../dv")
        return f"<span title='DV Document'><a href=\"{url}\">DV</a></span>"
    else:
        return ""


# Link the version to the commit id (if available).
def get_linked_version(rev):
    version = html.escape(rev['version'])
    tree = rev['commit_id'] if 'commit_id' in rev else 'master'
    url = f"https://github.com/lowrisc/opentitan/tree/{tree}"
    return f"<span title='{tree}'><a href=\"{url}\">{version}</a></span>"


# Link D/V stages with the checklist table.
def get_linked_checklist(obj, rev, stage, is_latest_rev=True):
    if not stage or stage not in rev:
        return ""

    url = ""
    in_page_ref = ""
    # if N/A or in D0/V0 stage, there is no in-page reference.
    if rev[stage] not in ["D0", "V0", "N/A"]:
        in_page_ref = f"#{html.escape(rev[stage]).lower()}"

    # If the checklist is available, the commit id is available, and it is not
    # the latest revision, link to the committed version of the checklist.
    # Else, if checklist is available, then link to the current version of the
    # checklist html.
    # Else, link to the template.
    if 'hw_checklist' in obj and 'commit_id' in rev and not is_latest_rev:
        url = (f"https://github.com/lowrisc/opentitan/tree/{rev['commit_id']}/"
               f"{obj['hw_checklist']}.md{in_page_ref}")
    elif 'hw_checklist' in obj:
        url = get_doc_url(obj['_ip_desc_hjson_dir'],
                          obj['hw_checklist'] + ".html" + in_page_ref)
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
                          obj['sw_checklist'] + ".html" + in_page_ref)
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
def gen_dashboard_row_html(config: Union[Path, Tuple[Path, Path]],
                           outfile: TextIO):
    """Generate summary HTML table row from an IP block's configuration data.

    Parameters
        ----------
        config : Union[
            Path,              # Path to a block configuration file
            Tuple[Path, Path], # Path to a block configuration file +
                                 Path to the block's ip documentation dir
        ]
            The source configuration data the table row is generated from.
        outfile : TextIO
            io object the generated HTML is written into.

    The Union of options for the 'config' argument allows us to handle some
    special cases, such as templated IP that are instantiated as part of the
    SoC generation process.
    e.g
    Path  ->  `hw/ip/aes/data/aes.hjson`
    Tuple -> (`hw/top_earlgrey/ip/clkmgr/data/autogen/clkmgr.hjson`,
              `hw/ip/clkmgr/`)
    """

    if isinstance(config, Tuple):
        hjson_path = config[0]
        ip_desc_hjson_dir = str((config[1] / "data").relative_to(REPO_TOP))
    else:
        hjson_path = config
        ip_desc_hjson_dir = str(hjson_path.parent.relative_to(REPO_TOP))

    try:
        with open(str(hjson_path)) as prjfile:
            try:
                obj = hjson.load(prjfile)
            except ValueError:
                raise SystemExit(sys.exc_info()[1])
    except IOError as e:
        log.error("Error opening file %s: %s", hjson_path, e)
        return

    if hjson_path.suffixes == ['.prj', '.hjson']:
        is_comportable_spec = False
    else:
        is_comportable_spec = True

    if dashboard_validate.validate(obj, is_comportable_spec) == 0:
        log.info("Generated dashboard object for " + str(hjson_path))
    else:
        log.fail("hjson file import failed\n")

    obj['_ip_desc_hjson_dir'] = ip_desc_hjson_dir

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
    genout(outfile, "        <td class=\"dv-doc\">" +
                    get_linked_dv_doc(obj) + "</td>\n")
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
            outstr += "        <td class='dv-doc'>"
            outstr += get_linked_dv_doc(obj) + "</td>\n"
        # Print out the module name in the first entry only
        elif i == 0:
            outstr += "        <td class='fixleft' rowspan='{}'>".format(
                len(revisions))
            outstr += get_linked_design_spec(obj) + "</td>\n"
            outstr += "        <td class='hw-stage' rowspan='{}'>".format(
                len(revisions))
            outstr += get_linked_dv_doc(obj) + "</td>\n"

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
