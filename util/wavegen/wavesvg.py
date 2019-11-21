# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# portions adapted from the javascript wavedrom.js
# https://github.com/drom/wavedrom/blob/master/wavedrom.js
# see LICENSE.wavedrom

import io
import logging as log

from wavegen import wavesvg_data

# Generate brick: follows wavedrom.js


def gen_brick(texts, extra, times):
    res = []

    # length of four indicates 2 phases each with 2 bricks
    if (len(texts) == 4):
        if extra != int(extra):
            log.error("Clock must have an integer period")
        for j in range(times):
            res.append(texts[0])
            for i in range(int(extra)):
                res.append(texts[1])
            res.append(texts[2])
            for i in range(int(extra)):
                res.append(texts[3])
        return res

    if (len(texts) == 1):
        t1 = texts[0]
    else:
        t1 = texts[1]

    res.append(texts[0])
    for i in range(times * int(2 * (extra + 1)) - 1):
        res.append(t1)
    return res


# Generate first brick in a line: follows wavedrom.js
def gen_first_wavebrick(text, extra, times):

    gentext = {
        'p': ['pclk', '111', 'nclk', '000'],
        'n': ['nclk', '000', 'pclk', '111'],
        'P': ['Pclk', '111', 'nclk', '000'],
        'N': ['Nclk', '000', 'pclk', '111'],
        'l': ['000'],
        'L': ['000'],
        '0': ['000'],
        'h': ['111'],
        'H': ['111'],
        '1': ['111'],
        '=': ['vvv-2'],
        '2': ['vvv-2'],
        '3': ['vvv-3'],
        '4': ['vvv-4'],
        '5': ['vvv-5'],
        'd': ['ddd'],
        'u': ['uuu'],
        'z': ['zzz']
    }
    return gen_brick(gentext.get(text, ['xxx']), extra, times)


# Generate subsequent bricks: text contains before and after states
# Follows wavedrom
def gen_wavebrick(text, extra, times):

    # new states that have a hard edge going in to them
    new_hardedges = {
        'p': 'pclk',
        'n': 'nclk',
        'P': 'Pclk',
        'N': 'Nclk',
        'h': 'pclk',
        'l': 'nclk',
        'H': 'Pclk',
        'L': 'Nclk'
    }

    # new state with a soft edge
    new_softedges = {
        '0': '0',
        '1': '1',
        'x': 'x',
        'd': 'd',
        'u': 'u',
        'z': 'z',
        '=': 'v',
        '2': 'v',
        '3': 'v',
        '4': 'v',
        '5': 'v'
    }

    # state we are coming from
    old_edges = {
        'p': '0',
        'n': '1',
        'P': '0',
        'N': '1',
        'h': '1',
        'l': '0',
        'H': '1',
        'L': '0',
        '0': '0',
        '1': '1',
        'x': 'x',
        'd': 'd',
        'u': 'u',
        'z': 'z',
        '=': 'v',
        '2': 'v',
        '3': 'v',
        '4': 'v',
        '5': 'v'
    }

    # tags (basically the colour) -- js had two arrays for this
    tags = {
        'p': '',
        'n': '',
        'P': '',
        'N': '',
        'h': '',
        'l': '',
        'H': '',
        'L': '',
        '0': '',
        '1': '',
        'x': '',
        'd': '',
        'u': '',
        'z': '',
        '=': '-2',
        '2': '-2',
        '3': '-3',
        '4': '-4',
        '5': '-5'
    }

    # drawing for the second half of the new state
    new_secondbricks = {
        'p': '111',
        'n': '000',
        'P': '111',
        'N': '000',
        'h': '111',
        'l': '000',
        'H': '111',
        'L': '000',
        '0': '000',
        '1': '111',
        'x': 'xxx',
        'd': 'ddd',
        'u': 'uuu',
        'z': 'zzz',
        '=': 'vvv-2',
        '2': 'vvv-2',
        '3': 'vvv-3',
        '4': 'vvv-4',
        '5': 'vvv-5'
    }

    phase2_firstbricks = {'p': 'nclk', 'n': 'pclk', 'P': 'nclk', 'N': 'pclk'}

    phase2_secondbricks = {'p': '000', 'n': '111', 'P': '000', 'N': '111'}

    xclude = {
        'hp': '111',
        'Hp': '111',
        'ln': '000',
        'Ln': '000',
        'nh': '111',
        'Nh': '111',
        'pl': '000',
        'Pl': '000'
    }

    secondbrick = new_secondbricks.get(text[1])
    hardbrick = new_hardedges.get(text[1])
    if hardbrick == None:
        # a soft edge gets the brick type constructed from the
        # old state, m, new state. Old and new states may have
        # tags which basically represent the colour
        newch = new_softedges.get(text[1])
        oldch = old_edges.get(text[0])
        if newch == None or oldch == None:
            # unknown: can't find the characters to make an edge
            return gen_brick(['xxx'], extra, times)
        else:
            # soft curves
            return gen_brick([
                oldch + 'm' + newch + tags[text[0]] + tags[text[1]],
                secondbrick
            ], extra, times)
    else:
        specialcase = xclude.get(text)
        if specialcase != None:
            hardbrick = specialcase

        # sharp curves
        twophase = phase2_firstbricks.get(text[1])
        if twophase == None:
            # hlHL
            return gen_brick([hardbrick, secondbrick], extra, times)
        else:
            # pnPN
            return gen_brick([
                hardbrick, secondbrick, twophase,
                phase2_secondbricks.get(text[1])
            ], extra, times)


# text is the wave member of the signal object
# extra = hscale-1 ( padding )


def parse_wavelane(text, extra):
    res = []
    pos = 1
    tlen = len(text)
    subCycle = False
    if tlen == 0:
        return res;
    next = text[0]

    repeats = 1
    while pos < tlen and (text[pos] == '.' or text[pos] == '|'):
        pos += 1
        repeats += 1

    res = gen_first_wavebrick(next, extra, repeats)

    while pos < tlen:
        top = next
        next = text[pos]
        pos += 1
        if next == '<':  # sub-cycles on
            subCycle = True
            next = text[pos]
            pos += 1

        if next == '>':  # sub-cycles off
            subCycle = False
            next = text[pos]
            pos += 1

        repeats = 1
        while pos < tlen and (text[pos] == '.' or text[pos] == '|'):
            pos += 1
            repeats += 1
        if subCycle:
            res.extend(gen_wavebrick(top + next, 0, repeats - lane.period))
        else:
            res.extend(gen_wavebrick(top + next, extra, repeats))

    # res is array of half brick types, each is item is string
    return res


def render_svghead(out, width, height, bricksused, svgn):
    out.write('  <svg id="svgcontent_' + str(svgn) + '"\n')
    out.write(wavesvg_data.head1)
    out.write('height="' + str(height) + '" width="' + str(width) + '"\n')
    out.write('viewBox="0 0 ' + str(width) + ' ' + str(height) + '">\n')
    out.write(wavesvg_data.head2)
    if len(bricksused) > 0:
        out.write(wavesvg_data.defs_head)
        for br in bricksused:
            out.write(wavesvg_data.use_defs[br])
        out.write(wavesvg_data.defs_tail)


def render_svgtail(out):
    out.write(wavesvg_data.tail)


def render_lanes_head(out, xoffset, yoffset, svgn):
    out.write('    <g id="lanes_' + str(svgn) + '" transform="translate(' +
              str(xoffset) + ', ' + str(yoffset) + ')">\n')


def render_events(out, svgn, events, edges):
    out.write('      <g id="wavearcs_' + str(svgn) + '">\n')
    for edge in edges:
        sp_edge = edge.split(None, 1)
        log.info("Edge " + str(edge) + " splits " + str(sp_edge))
        ev_from = events.get(sp_edge[0][0])
        ev_to = events.get(sp_edge[0][-1])
        shape = sp_edge[0][1:-1]
        if (len(sp_edge) > 1):
            label = sp_edge[1]
        else:
            label = ''

        if ev_from == None or ev_to == None or len(shape) < 1:
            log.warn("Could not find events for " + sp_edge[0])
            continue

        dx = ev_to[0] - ev_from[0]
        dy = ev_to[1] - ev_from[1]
        # lx,ly is the center of the label, it may be adjusted
        lx = (ev_to[0] + ev_from[0]) // 2
        ly = (ev_to[1] + ev_from[1]) // 2

        if shape[0] == '<' and shape[-1] == '>':
            path_s = 'marker-end:url(#arrowhead);' \
                     'marker-start:url(#arrowtail);stroke:#0041c4;' \
                     'stroke-width:1;fill:none'
            shape = shape[1:-1]
        elif shape[-1] == '>':
            path_s = 'marker-end:url(#arrowhead);stroke:#0041c4;' \
                     'stroke-width:1;fill:none'
            shape = shape[:-1]
        elif shape[0] == '<':
            path_s = 'marker-start:url(#arrowtail);stroke:#0041c4;' \
                     'stroke-width:1;fill:none'
            shape = shape[1:]
        else:
            path_s = 'fill:none;stroke:#00F;stroke-width:1'

        # SVG uses the case to indicate abs or relative
        path_type = 'M'
        # always start at the from point
        path_d = ' ' + str(ev_from)[1:-1]

        if shape == '~':
            path_d += (' c ' + str(0.7 * dx) + ', 0 ' + str(0.3 * dx) + ', ' +
                       str(dy) + ' ' + str(dx) + ', ' + str(dy))
        elif shape == '-~':
            path_d += (' c ' + str(0.7 * dx) + ', 0 ' + str(dx) + ', ' +
                       str(dy) + ' ' + str(dx) + ', ' + str(dy))
            lx = ev_from[0] + dx * 0.75
        elif shape == '~-':
            path_d += (' c 0, 0 ' + str(0.3 * dx) + ', ' + str(dy) + ' ' +
                       str(dx) + ', ' + str(dy))
            lx = ev_from[0] + dx * 0.25
        elif shape == '-|':
            path_d += ' ' + str(dx) + ',0 0,' + str(dy)
            path_type = 'm'
            lx = ev_to[0]
        elif shape == '|-':
            path_d += ' 0,' + str(dy) + ' ' + str(dx) + ',0'
            path_type = 'm'
            lx = ev_from[0]
        elif shape == '-|-':
            path_d += (' ' + str(dx / 2) + ',0 0,' + str(dy) + ' ' + str(
                dx / 2) + ',0')
            path_type = 'm'
        else:  # catch - here (and anything else)
            path_d += ' ' + str(ev_to)[1:-1]

        out.write('      <path id="gmark_' + sp_edge[0][0] + '_' +
                  sp_edge[0][-1] + '" d="' + path_type + path_d + '" style="' +
                  path_s + '"></path>\n')
        if len(label) != 0:
            out.write('        <rect height="9" '
                      'style="fill: rgb(255, 255, 255);" '
                      'width="' + str(5 * len(label)) + '" '
                      'x="' + str(lx - 2.5 * len(label)) + '" '
                      'y="' + str(ly - 8) + '"></rect>\n')
            out.write('      <text style="font-size: 10px;" '
                      'text-anchor="middle" xml:space="preserve" '
                      'x="' + str(lx) + '" y="' + str(ly) + '">'
                      '<tspan>' + label + '</tspan></text>\n')

    # Do events last so they are on top
    for e in events:
        log.info("Event " + e)
        if e.islower():
            (evx, evy) = events[e]
            # rectangles are taller than in js because it looks better to me
            out.write('        <rect y="' + str(evy - 8) + '" height="12" '
                      'x="' + str(evx - 3) + '" width="6" '
                      'style="fill: rgb(255, 255, 255);"></rect>\n')
            out.write('        <text style="font-size: 8px;" '
                      'x="' + str(evx) + '" y="' + str(evy) + '" '
                      'text-anchor="middle">' + e + '</text>\n')
    out.write('      </g>\n')


def render_wavelanes(out, xscale, yscale, lanes, svgn, events):
    lnum = 0
    x_edgeoff = 6
    for lane in lanes:
        phase = lane[5]

        out.write('      <g id="wavelane_' + str(svgn) + '_' + str(lnum) + '"'
                  ' transform="translate(0,' + str(lnum * yscale + 5) +
                  ')">\n')
        if len(lane[0]) != 0:
            out.write('        <text x="-15" y="15" class="info" '
                      'text-anchor="end" xml:space="preserve">'
                      '<tspan>' + lane[0] + '</tspan></text>\n')
        out.write('        <g id="wavelane_draw_' + str(svgn) + '_' +
                  str(lnum) + '" '
                  'transform="translate(0,0)">\n')
        if phase < 0:
            bnum = abs(phase)
            lstart = 0
        else:
            bnum = 0
            lstart = phase

        for x in lane[1][lstart:]:
            out.write('          <use xlink:href="#' + x + '" '
                      'transform="translate(' + str(bnum * xscale) +
                      ')"></use>\n')
            bnum += 1
        dpos = 0
        dend = len(lane[3])
        period = lane[4]
        if phase < 0:
            i = 0
        else:
            # start point ensures bnum below is never less than -1
            i = phase // 2

        if dend > 0 and lane[3][-1] == '!cdata!':
            lane[3].pop()
            dend -= 1;
            labelif = '01=2345ud'
        else:
            labelif = '=2345'

        scan_max = max(len(lane[2]), len(lane[6]))
        while (i < scan_max):
            bnum = i * 2 - phase

            if (i < len(lane[2])):
                x = lane[2][i]
                if dpos < dend and x in labelif:
                    nslot = 1
                    while (i + nslot) < len(
                            lane[2]) and lane[2][i + nslot] == '.':
                        nslot += 1
                    xcenter = period * xscale * nslot + bnum * period * xscale
                    # the center needs to be offset by the width of the
                    # edge because that lives in the first brick
                    xcenter += x_edgeoff
                    out.write('        <text x="' + str(xcenter))
                    out.write('" y="' + str(yscale / 2) + '" '
                              'text-anchor="middle" xml:space="preserve">')
                    tspan_or_text(out, lane[3][dpos], True)
                    out.write('</text>')
                    dpos = dpos + 1
                if x == '|':
                    # render a gap (this diverges from how the js does it
                    # where it is in a different g
                    out.write('        <use xlink:href="#gap" transform="'
                              'translate(' +
                              str(period * (bnum * xscale + xscale)) + ')"'
                              '></use>\n')

            if i < len(lane[6]):
                ev = lane[6][i]
                if ev != '.':
                    events[ev] = (period * bnum * xscale + x_edgeoff,
                                  lnum * yscale + 2 + yscale // 2)
            i += 1

        out.write('        </g>\n      </g>\n')
        lnum += 1


def render_marks(out, nbricks, xscale, ylen, svgn):
    out.write('      <g id="gmarks_' + str(svgn) + '">\n')
    mnum = 0
    for i in range(nbricks // 2):
        out.write('        <path id="gmark_' + str(svgn) + '_' + str(mnum) +
                  '" '
                  'd="m ' + str(i * 2 * xscale) + ',0 0,' + str(ylen) + '" '
                  'style="stroke: rgb(136, 136, 136); '
                  'stroke-width:0.5; stroke-dasharray:1,3"'
                  '></path>\n')
        mnum += 1
    out.write('      </g>\n')


def tspan_or_text(out, text, outerspan):
    if isinstance(text, str):
        if outerspan: out.write('<tspan>')
        out.write(text)
        if (outerspan): out.write('</tspan>')
    else:
        if text[0] != 'tspan':
            log.warn('Expecting tspan, got ' + str(text[0]))
            return
        if len(text) == 3 and isinstance(text[1], dict):
            out.write('<tspan ')
            for x in text[1]:
                out.write(x + '="' + text[1][x] + '" ')
            out.write('>')
            tspan_or_text(out, text[2], False)
        else:
            out.write('<tspan>')
            for x in text[1:]:
                tspan_or_text(out, x, False)
        out.write('</tspan>')


def render_caption(out, text, nbricks, xscale, yoffset):
    out.write('        <text x="' + str(nbricks * xscale // 2) + '" '
              'y="' + str(yoffset) + '" '
              ' text-anchor="middle" fill="#000" xml:space="preserve">')
    tspan_or_text(out, text, True)
    out.write('</text>\n')


def render_ticktock(out, info, xoff, xsep, yoff, num):
    # info could be a number/string representing the lowest tick number
    # or a string containing a list of space separated labels
    # or a list containing separate strings or a single string

    if isinstance(info, int) or (isinstance(info, str) and info.isdecimal()):
        base = int(info)
        for i in range(num):
            out.write('<text x="' + str(xoff + i * xsep) + '" y="' +
                      str(yoff) + '" '
                      'text-anchor="middle" class="muted" xml:space="preserve"'
                      '>' + str(i + base) + '</text>\n')
    else:
        if isinstance(info, list):
            if len(info) == 1:
                labels = info[0].split()
            else:
                labels = info
        else:
            labels = info.split()
        if num > len(labels):
            num = len(labels)
        for i in range(num):
            out.write('<text x="' + str(xoff + i * xsep) + '" y="' +
                      str(yoff) + '" '
                      'text-anchor="middle" class="muted" xml:space="preserve"'
                      '>' + labels[i] + '</text>\n')


def render_lanes_tail(out):
    out.write('    </g>\n')


# group array is [0=Name, 1=startlane, 2=endlane+1, 3=depth]
def render_groups(out, groups, yhead, yoff, snum):
    gdepth = 0
    if len(groups) == 0:
        return

    for gr in groups:
        if gr[3] > gdepth:
            gdepth = gr[3]
    xgoff = 80 - gdepth * 25

    out.write('    <g id="groups_' + str(snum) + '">\n')

    gnum = 0
    for gr in groups:
        ymin = yhead + gr[1] * yoff
        ylen = (gr[2] - gr[1]) * yoff

        out.write('      <path id="group_' + str(snum) + '_' + str(gnum) +
                  '" ')
        out.write('d="m ' + str(xgoff + 25 * gr[3]) + ',' + str(ymin + 3.5) +
                  ' c -3,0 -5,2 -5,5 l 0,' + str(ylen - 16) + ' c 0,3 2,5 5,5"'
                  'style="stroke: rgb(0, 65, 196); stroke-width: 1; '
                  'fill: none;"></path>\n')
        if len(gr[0]) > 0:
            out.write('      <g transform="translate(' +
                      str(xgoff - 10 + 25 * gr[3]) + ',' +
                      str(ymin + ylen // 2) + ')">\n')
            out.write('        <g transform="rotate(270)">\n')
            out.write('          <text text-anchor="middle" class="info" '
                      'xml:space="preserve"><tspan>' + gr[0] +
                      '</tspan></text>\n        </g>\n      </g>')
        gnum += 1
    out.write('    </g>\n')


def parse_wave(x, hscale, lanes, groups, gdepth, bricksused):
    sname = ""
    wave = ''
    node = ''
    labels = []
    bricks = []
    extra = hscale - 1
    phase = 0
    xmax = 0
    global prevdefs

    if isinstance(x, list):
        gname = x[0]
        startlane = len(lanes)
        for y in x[1:]:
            ymax = parse_wave(y, hscale, lanes, groups, gdepth + 1, bricksused)
            if ymax > xmax:
                xmax = ymax
        groups.append([gname, startlane, len(lanes), gdepth])
        return xmax

    if 'name' in x:
        sname = x['name']

    # period must be before wave because it changes extra
    if 'period' in x:
        fp = float(x['period'])
        if fp < 0 or fp * 2 != int(fp * 2):
            log.error("Period must be integer or 0.5")
        extra = hscale * fp - 1
    if 'phase' in x:
        phase = int(x['phase'] * 2)
    if 'wave' in x:
        wave = x['wave']
        bricks = parse_wavelane(wave, extra)
        for br in bricks:
            if not br in bricksused and not br in prevdefs:
                bricksused.append(br)
        if 'data' in x:
            labels = x['data']
            if isinstance(labels, str):
                labels = labels.split()
        if 'cdata' in x:
            labels = x['cdata']
            if isinstance(labels, str):
                labels = labels.split()
            labels.append('!cdata!')

    if 'node' in x:
        node = x['node']

    lanes.append([sname, bricks, wave, labels, extra + 1, phase, node])
    return len(bricks)


# obj is Hjson parsed object with wavejson
# svg_num is a number that makes this svg unique. First one must be 0


def convert(obj, svg_num):
    xs = 20  # x scale = width of cycle
    ys = 20  # y scale = height of wave
    yo = int(ys * 1.5)  # y offest between lines of waves
    xg = 150  # xoffset of waves (space for names and groups)
    yh0 = 0  # height allocated for header tick/tock labels
    yh1 = 0  # height allocated for header string
    headtext = ''  # header string
    headticktock = 0  # does header have tick=1/tock=2
    yf0 = 0  # height allocated for footer tick/tock labels
    yf1 = 0  # height allocated for footer string
    foottext = ''  # footer string
    footticktock = 0  # does footer have tick=1/tock=2
    global prevdefs  # holds bricks previously defined
    events = {}

    if svg_num == 0:
        bricksused = ['gap']
        prevdefs = []
    else:
        bricksused = []

    # section was parseConfig in js
    if 'config' in obj and 'hscale' in obj['config']:
        hscale = int(obj['config']['hscale'])
        log.info("Set hscale to " + str(hscale))
    else:
        hscale = 1

    if 'head' in obj:
        head = obj['head']
        if 'tick' in head:
            yh0 = 20
            headtt = head['tick']
            headticktock = 1
        elif 'tock' in head:
            yh0 = 20
            headtt = head['tock']
            headticktock = 2

        if 'text' in head:
            yh1 = 46
            headtext = head['text']

    if 'foot' in obj:
        foot = obj['foot']
        if 'tick' in foot:
            yf0 = 20
            foottt = foot['tick']
            footticktock = 1
        elif 'tock' in foot:
            yf0 = 20
            foottt = foot['tock']
            footticktock = 2

        if 'text' in foot:
            yf1 = 46
            foottext = foot['text']

    if 'edge' in obj:
        if 'arrows' not in prevdefs:
            bricksused.append('arrows')
        edges = obj['edge']
        log.info("Got edge: " + str(edges))
    else:
        edges = []

    # build the signal bricks array

    lanes = []
    groups = []
    xmax = 0
    if 'signal' in obj:
        for x in obj['signal']:
            xlen = parse_wave(x, hscale, lanes, groups, 0, bricksused)
            if xlen > xmax:
                xmax = xlen

    log.info("Got " + str(len(lanes)) + " lanes. xmax is " + str(xmax))
    log.info(str(lanes))

    outbuf = io.StringIO()

    height = len(lanes) * yo + yh0 + yh1 + yf0 + yf1
    width = xg + xmax * xs + xs
    wheight = len(lanes) * yo

    render_svghead(outbuf, width, height, bricksused, svg_num)
    render_lanes_head(outbuf, xg, yh0 + yh1, svg_num)
    render_marks(outbuf, xmax, xs, wheight, svg_num)
    if yh1 != 0:
        render_caption(outbuf, headtext, xmax, xs, -33 if yh0 != 0 else -13)

    if yf1 != 0:
        render_caption(outbuf, foottext, xmax, xs,
                       wheight + (45 if yf0 != 0 else 25))

    if headticktock == 1:
        render_ticktock(outbuf, headtt, 0, 2 * xs, -5, xmax // 2)
    if headticktock == 2:
        render_ticktock(outbuf, headtt, xs, 2 * xs, -5, xmax // 2)

    if footticktock == 1:
        render_ticktock(outbuf, foottt, 0, 2 * xs, wheight + 15, xmax // 2)
    if footticktock == 2:
        render_ticktock(outbuf, foottt, xs, 2 * xs, wheight + 15, xmax // 2)

    render_wavelanes(outbuf, xs, yo, lanes, svg_num, events)
    if (len(events) > 0):
        render_events(outbuf, svg_num, events, edges)
    render_lanes_tail(outbuf)
    render_groups(outbuf, groups, yh0 + yh1, yo, svg_num)
    render_svgtail(outbuf)
    prevdefs.extend(bricksused)

    generated = outbuf.getvalue()
    outbuf.close()
    return generated
