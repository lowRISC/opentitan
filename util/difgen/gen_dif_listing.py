# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Generate HTML documentation for Device Interface Functions (DIFs)
"""

import copy
import logging as log
import subprocess
import xml.etree.ElementTree as ET


# Turn the Doxygen multi-file XML output into one giant XML file (and parse it
# into a python object), using the provided XLST file.
def get_combined_xml(doxygen_xml_path):
    xsltproc_args = [
        "xsltproc",
        str(doxygen_xml_path.joinpath("combine.xslt")),
        str(doxygen_xml_path.joinpath("index.xml")),
    ]

    combined_xml_res = subprocess.run(xsltproc_args, check=True,
        cwd=str(doxygen_xml_path), stdout=subprocess.PIPE,
        universal_newlines=True)
    return ET.fromstring(combined_xml_res.stdout)

# Get all information about individual DIF functions that are specified in one
# DIF header. This returns only the Info from the XML that we require.
def get_difref_info(combined_xml, dif_header):
    compound = _get_dif_file_compound(combined_xml, dif_header)
    if compound == None:
        return []

    file_id = _get_dif_file_id(compound)
    functions = _get_dif_function_info(compound, file_id)
    return functions

# Create HTML List of DIFs, using the info from the combined xml
def gen_listing_html(combined_xml, dif_header, dif_listings_html):
    compound = _get_dif_file_compound(combined_xml, dif_header)
    if compound == None:
        log.error("Doxygen output not found for {}".format(dif_header))
        return

    file_id = _get_dif_file_id(compound)
    functions = _get_dif_function_info(compound, file_id)

    if len(functions) == 0:
        log.error("No DIF functions found for {}".format(dif_header))
        return

    # Generate DIF listing header
    dif_listings_html.write('<p>To use this DIF, include the following C header:</p>')
    dif_listings_html.write('<pre><code class=language-c data-lang=c>')
    dif_listings_html.write('#include "<a href="/sw/apis/{}.html">{}</a>"'.format(file_id, dif_header))
    dif_listings_html.write('</code></pre>\n')

    # Generate DIF function list.
    dif_listings_html.write('<p>This header provides the following device interface functions:</p>')
    dif_listings_html.write('<ul>\n')
    for f in sorted(functions, key=lambda x: x['name']):
        dif_listings_html.write('<li title="{prototype}" id="Dif_{name}">'.format(**f))
        dif_listings_html.write('<a href="{full_url}">'.format(**f))
        dif_listings_html.write('<code>{name}</code>'.format(**f))
        dif_listings_html.write('</a>\n')
        dif_listings_html.write(f['description'])
        dif_listings_html.write('</li>\n')
    dif_listings_html.write('</ul>\n')

# Generate HTML link for single function, using info returned from
# get_difref_info
def gen_difref_html(function_info, difref_html):
    difref_html.write('<a href="{full_url}">'.format(**function_info))
    difref_html.write('<code>{name}</code>'.format(**function_info))
    difref_html.write('</a>\n')

def _get_dif_file_compound(combined_xml, dif_header):
    for c in combined_xml.findall('compounddef[@kind="file"]'):
        if c.find("location").attrib["file"] == dif_header:
            return c
    return None

def _get_dif_file_id(compound):
    return compound.attrib["id"]

def _get_dif_function_info(compound, file_id):
    funcs = compound.find('sectiondef[@kind="func"]')
    if funcs == None:
        return []

    # Collect useful info on each function
    functions = []
    for m in funcs.findall('memberdef[@kind="function"]'):
        func_id = m.attrib['id']
        # Strip refid prefix, which is separated from the funcid by `_1`
        if func_id.startswith(file_id + '_1'):
            # The +2 here is because of the weird `_1` separator
            func_id = func_id[len(file_id) + 2:]
        else:
            # I think this denotes that this function isn't from this file
            continue

        func_info = {}
        func_info["id"] = m.attrib["id"]
        func_info["file_id"] = file_id
        func_info["local_id"] = func_id
        func_info["full_url"] = "/sw/apis/{}.html#{}".format(file_id, func_id)

        func_info["name"] = _get_text_or_empty(m, "name")
        func_info["prototype"] = _get_text_or_empty(
            m, "definition") + _get_text_or_empty(m, "argsstring")
        func_info["description"] = _get_html_or_empty(m,
                                                      "briefdescription/para")

        functions.append(func_info)

    return functions


def _get_html_or_empty(element: ET.Element, xpath: str) -> str:
    """ Get a minimal HTML-rendering of the children in an element.

    element is expected to be a docCmdGroup according to the DoxyGen schema [1],
    but only a very minimal subset of formatting is transferred to semantic
    HTML. However, the tag structure is retained by transforming all tags into
    HTML `span` tags with a class attribute `doxygentag-ORIGINALTAGNAME`. This
    can be used to write CSS targeting specific Doxygen tags and recreate the
    intended formatting.

    In addtion, the following semantic transformations are performed:
    - `computeroutput` is transformed to `code`

    [1] https://github.com/doxygen/doxygen/blob/master/templates/xml/compound.xsd"""
    inner = element.find(xpath)
    # if the element isn't found, return ""
    if inner is None:
        return ""

    # Avoid modifying the passed element argument.
    inner_copy = copy.deepcopy(inner)

    for c in inner_copy.iter():
        c.set('class', 'doxygentag-' + c.tag)
        if c.tag == 'computeroutput':
            c.tag = 'code'
        else:
            c.tag = 'span'

    # Create a string from all subelements
    text = ET.tostring(inner_copy, encoding="unicode", method="html")
    return text or ""


def _get_text_or_empty(element: ET.Element, xpath: str) -> str:
    """ Get all text of an element, without any tags """
    inner = element.find(xpath)
    if inner is None:
        return ""

    return ' '.join([e for e in inner.itertext()]) or ""
