#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import json
import logging
import os
import os.path
import re
import subprocess
import sys
from collections import defaultdict

parser = argparse.ArgumentParser(
    description='Mapfile converter and visualizer')
parser.add_argument('--json',
                    default='',
                    help='Emit the mapfile as json to the named file')
parser.add_argument('--html',
                    default='',
                    help='Emit a mapfile visualization to the named file')
parser.add_argument('--regions',
                    default='rom,ram_main,eflash',
                    help='Which memory regions to analyze')
parser.add_argument('mapfile',
                    metavar='MAPFILE',
                    type=str,
                    help='Mapfile to process')
parser.add_argument('-v',
                    '--view',
                    default=False,
                    action=argparse.BooleanOptionalAction,
                    help='Open the generated html in a browser')
parser.add_argument('-d',
                    '--dimensions',
                    default='1920x1080',
                    type=str,
                    help='Set the dimensions of the generated html diagram')
parser.add_argument('-a',
                    '--arrangement',
                    default='file',
                    type=str,
                    choices=['region', 'file'],
                    help='Arrange the hierarchy by this condition')
parser.add_argument('--ignore-debug',
                    default=True,
                    action=argparse.BooleanOptionalAction,
                    help='Ignore debug sections in the mapfile')

######################################################################
# A simple d3.js visualization: a nested tree map.
#
# Inspired by this example:
#   https://observablehq.com/@d3/nested-treemap
######################################################################
D3_TEMPLATE = r"""<!DOCTYPE html>
<div id="container"></div>
<script src="https://unpkg.com/@observablehq/stdlib@3"></script>
<script type="module">
import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7/+esm";
var data = @DATA@;

// Specify the chart’s dimensions.
const width = @WIDTH@;
const height = @HEIGHT@;
const tile = d3.treemapSquarify;
const {DOM} = new observablehq.Library;

const color = d3.scaleSequential([8, 0], d3.interpolateMagma);

// Create the treemap layout.
const treemap = data => d3.treemap()
  .size([width, height])
  .paddingOuter(3)
  .paddingTop(19)
  .paddingInner(1)
  .round(true)
(d3.hierarchy(data)
    .sum(d => d.size)
    .sort((a, b) => b.size - a.size));
const root = treemap(data);

// Create the SVG container.
const svg = d3.create("svg")
    .attr("width", width)
    .attr("height", height)
    .attr("viewBox", [0, 0, width, height])
    .attr("style", "max-width: 100%; height: auto; overflow: visible; font: 10px sans-serif;");

const shadow = DOM.uid("shadow");

svg.append("filter")
    .attr("id", shadow.id)
  .append("feDropShadow")
    .attr("flood-opacity", 0.3)
    .attr("dx", 0)
    .attr("stdDeviation", 3);

const node = svg.selectAll("g")
  .data(d3.group(root, d => d.height))
  .join("g")
    .attr("filter", shadow)
  .selectAll("g")
  .data(d => d[1])
  .join("g")
    .attr("transform", d => `translate(${d.x0},${d.y0})`);

function maybe_size(sz) {
  if (sz) return "(0x" + sz.toString(16) + ")";
  return "";
}

function symlist(d) {
  if (d.children) {
      return d.children.map(d => symlist(d)).join("\n");
  } else if (d.data.symbols.length) {
    return d.data.symbols.map(
        d => d.name + ": 0x" + d.addr.toString(16) + maybe_size(d.size)
    ).join("\n");
  } else {
    return "(noname): 0x" + d.data.addr.toString(16) + maybe_size(d.data.size);
  }
}

// Append a tooltip.
const format = d3.format(",d");
node.append("title")
    .text(d =>
`${d.ancestors().reverse().map(d => d.data.name).join(".")}
Size: ${format(d.value)}
Symbols:
${symlist(d)}`);

node.append("rect")
    .attr("id", d => (d.nodeUid = DOM.uid("node")).id)
    .attr("fill", d => color(d.height))
    .attr("width", d => d.x1 - d.x0)
    .attr("height", d => d.y1 - d.y0);

node.append("clipPath")
    .attr("id", d => (d.clipUid = DOM.uid("clip")).id)
  .append("use")
    .attr("xlink:href", d => d.nodeUid.href);

node.append("text")
    .attr("clip-path", d => d.clipUid)
  .selectAll("tspan")
  .data(d => d.data.name.split(/(?=[A-Z][^A-Z])/g).concat(format(d.value)))
  .join("tspan")
    .attr("fill-opacity", (d, i, nodes) => i === nodes.length - 1 ? 0.7 : null)
    .text(d => d);

node.filter(d => d.children).selectAll("tspan")
    .attr("dx", 3)
    .attr("y", 13);

node.filter(d => !d.children).selectAll("tspan")
    .attr("x", 3)
    .attr("y", (d, i, nodes) => `${(i === nodes.length - 1) * 0.3 + 1.1 + i * 0.9}em`);

container.append(svg.node());
</script>
"""


class Mapfile(object):
    CLANG_LLD = 'clang_lld'
    GNU_LD = 'gnu_ld'

    def __init__(self, regions=('rom', 'ram_main'), ignore_debug=True):
        self.sections = []
        self.memory = {
            # It appears the clang-lld mapfile doesn't include the memory layout.
            # Punt and supply the earlgrey layout.
            'ram_ret_aon': (0x40600000, 0x40601000),
            'eflash': (0x20000000, 0x20100000),
            'ram_main': (0x10000000, 0x10020000),
            'rom': (0x00008000, 0x00010000),
            'rom_ext_virtual': (0x90000000, 0x90080000),
            'owner_virtual': (0xa0000000, 0xa0080000),
        }
        self.regions = regions
        self.ignore_debug = ignore_debug

    def get_region(self, addr):
        """Given an address, get the name of the containing region."""
        for name, region in self.memory.items():
            if addr in range(*region):
                return name
        return None

    def parse_memory_config(self, f):
        """Parse the 'Memory Configuration' section of the mapfile."""
        found = False
        while True:
            line = f.readline()
            if not line:
                break
            line = line.strip()
            if 'VMA' in line and 'LMA' in line and 'Size' in line:
                return self.CLANG_LLD
            if line == 'Memory Configuration':
                found = True
                break

        if not found:
            return None

        self.memory = {}
        while True:
            line = f.readline().strip()
            if not line:
                continue
            if line == 'Linker script and memory map':
                break
            if 'Name' in line and 'Attributes' in line:
                continue
            field = re.split(r'\s+', line)
            name = field[0]
            addr = int(field[1], 0)
            size = int(field[2], 0)
            self.memory[name] = (addr, addr + size)
        return self.GNU_LD

    @staticmethod
    def object_file(section, addr, size, comment):
        """Create a dictionary representing an object file in the map."""
        path = None
        archive = None
        filename = None
        if comment:
            # Trim the `bazel-out/.../bin/` portion from the pathname and extract
            # the archive filename and internal filename.
            if m := re.match(r'^.*/bin/([^(]+)(?:\((.+)\))?$', comment):
                path = m.group(1).replace('_on_device_do_not_use_directly', '')
                archive = os.path.basename(path)
                filename = m.group(2)
        return {
            'name': section.strip('.'),
            'addr': addr,
            'size': size,
            'path': path,
            'archive': archive,
            'filename': filename,
            'children': [],
            'symbols': [],
        }

    @staticmethod
    def parse_int(v, base):
        return int(v, base) if v is not None else None

    def parse_sections_gnu(self, f):
        """Parse the 'memory map' section of a gnu-ld mapfile."""
        # These regexes borrowed from linkermapviz:
        # https://github.com/PromyLOPh/linkermapviz
        sec_re = re.compile(
            '(?P<section>.+?|.{14,}\n)[ ]+0x(?P<offset>[0-9a-f]+)[ ]+' +
            '0x(?P<size>[0-9a-f]+)(?:[ ]+(?P<comment>.+))?\n+', re.I)
        sub_re = re.compile(
            '[ ]{16}0x(?P<offset>[0-9a-f]+)[ ]+(?P<function>.+)\n+', re.I)
        f = f.read()
        pos = 0
        sections = []
        while True:
            m = sec_re.match(f, pos)
            if not m:
                try:
                    pos = f.index('\n', pos) + 1
                    continue
                except ValueError:
                    break
            pos = m.end()
            section = m.group('section')
            addr = self.parse_int(m.group('offset'), 16)
            size = self.parse_int(m.group('size'), 16)
            comment = m.group('comment')

            ssection = section.strip()
            if self.ignore_debug and ssection.startswith('.debug_'):
                continue

            if self.get_region(addr) in self.regions and size > 0:
                if ssection.startswith('.'):
                    ssection = ssection[1:]
                obj = self.object_file(ssection, addr, size, comment)
                if section.startswith(' '):
                    parent = sections[-1]['name'] + '.'
                    if obj['name'].startswith(parent):
                        obj['name'] = obj['name'][len(parent):]
                    sections[-1]['children'].append(obj)
                    while True:
                        if m := sub_re.match(f, pos):
                            pos = m.end()
                            addr = self.parse_int(m.group('offset'), 16)
                            func = m.group('function')
                            if ('=' in func or 'ASSERT' in func or
                                    'ALIGN' in func):
                                continue
                            if sections:
                                sections[-1]['children'][-1]['symbols'].append(
                                    {
                                        'name': func,
                                        'addr': addr,
                                    })
                        else:
                            break
                else:
                    sections.append(obj)
        self.sections = sections

    def parse_clang_lld(self, f):
        """Parse a clang-lld mapfile."""
        map_re = re.compile(
            # The first 4 columns are VMA, LMA, Size and Alignment.
            r'(?P<vma>[0-9a-f]+)\s+(?P<lma>[0-9a-f]+)\s+(?P<size>[0-9a-f]+)\s+(?P<align>\d+)\s'
            # Followed by one of section, symbol or filename.
            r'((?P<section>[^ ]+)|\s{16}(?P<symbol>[^ ]*)|\s{8}(?P<file>[^ ]*))'
        )
        sections = []
        for line in f:
            line = line.strip()
            # Discard linker-generated symbols and lines that don't match the regex.
            if '=' in line:
                continue
            m = map_re.match(line)
            if not m:
                continue
            addr = self.parse_int(m.group('vma'), 16)
            size = self.parse_int(m.group('size'), 16)
            if self.get_region(addr) not in self.regions or size == 0:
                # Skip things that aren't in our regions.
                continue
            section = m.group('section')
            symbol = m.group('symbol')
            file = m.group('file')
            if section:
                # Section information
                if self.ignore_debug and section.startswith('.debug_'):
                    continue
                sections.append(self.object_file(section, addr, size, ''))
            elif file:
                # File and section information.
                parent = '.' + sections[-1]['name']
                file, section = file.split(':')
                section = section.strip('()')
                if self.ignore_debug and section.startswith('.debug_'):
                    continue
                if section.startswith(parent):
                    section = section[len(parent):]
                obj = self.object_file(section, addr, size, file)
                sections[-1]['children'].append(obj)
            elif symbol and sections:
                # Info about an individual symbol.
                sections[-1]['children'][-1]['symbols'].append(
                    dict(
                        name=symbol,
                        addr=addr,
                    ))
        self.sections = sections

    def parse(self, filename):
        """Parse the given mapfile."""
        with open(filename) as f:
            linker = self.parse_memory_config(f)
            if linker == self.GNU_LD:
                self.parse_sections_gnu(f)
            elif linker == self.CLANG_LLD:
                self.parse_clang_lld(f)
            else:
                raise Exception(
                    'Failed to detect type of mapfile (clang or gnu)')

    def by_memory_region(self):
        """Return the mapfile arranged by memory region."""
        region = {}
        for sec in self.sections:
            r = self.get_region(sec['addr'])
            if r not in region:
                region[r] = {
                    'name': r,
                    'addr': self.memory[r][0],
                    'size': self.memory[r][1] - self.memory[r][0],
                    'children': [],
                    'symbols': [],
                }
            region[r]['children'].append(sec)
        top = {
            'name': 'all',
            'children': list(region.values()),
            'symbols': [],
        }
        return top

    def by_filename(self):
        top = self.by_memory_region()
        for region in top['children']:
            for section in region['children']:
                files = defaultdict(list)
                for file in section['children']:
                    files[file['filename']].append(file)
                section['children'] = [
                    dict(name='[{}]'.format(name), children=info)
                    for name, info in files.items()
                ]
        return top

    def sum_children(self, item):
        """Sum up children and report discrepancies between sizes."""
        name = item.get('name', '__unknown__')
        size = item.get('size', 0)
        children = item.get('children', [])
        csz = 0
        for c in children:
            csz += self.sum_children(c)
        if csz == 0:
            csz = size
        else:
            item.pop('size', 0)
            item['computed_size'] = csz
        if size and csz != size:
            logging.warning(f'warn: {name} size {size} != computed_size {csz}')
        return csz


def main(args):
    m = Mapfile(regions=args.regions.split(','),
                ignore_debug=args.ignore_debug)
    m.parse(args.mapfile)
    if args.arrangement == 'region':
        regions = m.by_memory_region()
    elif args.arrangement == 'file':
        regions = m.by_filename()
    else:
        raise Exception('Unknown arrangement type:', args.arrangement)
    m.sum_children(regions)
    text = json.dumps(regions, indent=4)
    if args.json:
        with open(args.json, 'wt') as f:
            f.write(text)
    if args.html or args.view:
        filename = args.html if args.html else os.path.basename(
            args.mapfile).replace('.map', '') + '.html'
        width, height = args.dimensions.split('x')
        with open(filename, 'wt') as f:
            f.write(
                D3_TEMPLATE.replace('@DATA@',
                                    text).replace('@WIDTH@', width).replace(
                                        '@HEIGHT@', height))
        if args.view:
            subprocess.call(['xdg-open', filename])
    return 0


if __name__ == '__main__':
    args = parser.parse_args()
    sys.exit(main(args))

# vim: set ts=4 sts=4 sw=4 expandtab:
