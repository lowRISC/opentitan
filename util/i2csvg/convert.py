# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Convert I2C host format to SVG

import logging as log
from collections import namedtuple

import i2csvg.i2csvg_data as sdata


# validating version of int(x, 0)
# returns int value, error flag
# if error flag is True value will be zero
def check_int(x, err_prefix):
    if isinstance(x, int):
        return x, False
    if len(x) == 0:
        log.error(err_prefix + " Zero length string")
        return 0, True
    if x[0] == '0' and len(x) > 2:
        if x[1] in 'bB':
            validch = '01'
        elif x[1] in 'oO':
            validch = '01234567'
        elif x[1] in 'xX':
            validch = '0123456789abcdefABCDEF'
        else:
            log.error(err_prefix +
                      ": int must start digit, 0b, 0B, 0o, 0O, 0x or 0X")
            return 0, True
        for c in x[2:]:
            if not c in validch:
                log.error(err_prefix + ": Bad character " + c + " in " + x)
                return 0, True
    else:
        if not x.isdecimal():
            log.error(err_prefix + ": Number not valid int " + x)
            return 0, 1
    return int(x, 0), False


def check_single(line, char, fullline, err):
    ''' Check for character char in input line
        Return True if there is one (or more)
        Propagate err or force to err True if more than one char
    '''
    res = False
    if char in line:
        res = True
        if line.count(char) > 1:
            log.warning('Multiple ' + char + ' in line ' + fullline)
            err = True
    return res, err


I2cOp = namedtuple('I2cOp',
                   'read rcont start stop nackok mvalue adr size fbyte tag')


def check_and_size(iic, line):
    ''' Check I2C Op for validity and return size in bits
    '''
    err = False
    if iic.start and iic.read:
        log.error('Start and Read found in ' + line)
        err = True
    if iic.rcont and not iic.read:
        log.error('RCont without Read found in ' + line)
        err = True

    # documentation says R+C and P is not permitted, but I think it
    # is needed for protocols where the last read data is ACKed?
    # (these don't match I2C or SMBus spec but exist in the wild)

    size = 0
    if iic.start:
        size += 1
    if iic.stop:
        size += 1
    if iic.read:
        # multi is D0, D1, ..., Dn-1 so 3 byte/acks and a 1 bit squiggle
        # regular read is one byte/ack per
        size += 9 * 3 + 1 if iic.mvalue else 9 * iic.fbyte
    else:
        # write data is one byte/ack
        size += 9
    # rcont, nackok just affect the polarity of the final ack bit
    # adr just affects how the write data is drawn
    return size, err


def parse_i2c_fifodata(line):
    ''' Parse input line of I2C FDATA fifo and convert to internal type
        Line is usually 0x + the hex value written to the register
        But could be binary (0b), octal (0o) or decimal
    '''
    fifodata, err = check_int(line, 'FIFO value')
    # bit values here must match the register definition!
    ress = (fifodata & 0x0100) != 0
    resp = (fifodata & 0x0200) != 0
    resr = (fifodata & 0x0400) != 0
    resc = (fifodata & 0x0800) != 0
    resn = (fifodata & 0x1000) != 0
    resb = fifodata & 0xff
    resm = False  # only used in descriptive case
    resa = False  # only used in descriptive case

    tmpr = I2cOp(resr, resc, ress, resp, resn, resm, resa, 0, resb, None)
    size, serr = check_and_size(tmpr, line)
    if serr:
        err = True
    return I2cOp(resr, resc, ress, resp, resn, resm, resa, size, resb,
                 None), err


def parse_i2c_code(line):
    ''' Parse input line of I2C FDATA fifo and convert to internal type
        Line is coded with flags and an 8-bit data value
        S - Start flag, P - stop flag,
        R - read flag, C - continue read flag, N - NackOk flag
        followed by the data byte
        Special cases:
        M - indicates multiple bytes instead of data byte
        A - followed by 0 or 1 address/direction or 2 address/data
        Data value in quotes is a tag
    '''
    resr, resc, ress, resp, resn = False, False, False, False, False
    resm, resa, resb = False, False, 0

    err = False
    firstval = 0
    for i in line:
        if i.isdigit() or i == "'":
            break
        firstval += 1
    # Will only check the flags section, so no concern about hex digits
    ress, err = check_single(line[:firstval], 'S', line, err)
    resp, err = check_single(line[:firstval], 'P', line, err)
    resr, err = check_single(line[:firstval], 'R', line, err)
    resc, err = check_single(line[:firstval], 'C', line, err)
    resn, err = check_single(line[:firstval], 'N', line, err)
    # these two are formally part of the value but parse like flags
    resm, err = check_single(line[:firstval], 'M', line, err)
    resa, err = check_single(line[:firstval], 'A', line, err)

    if firstval == len(line):
        if not resm:
            err = True
            log.error('No value found in ' + line)
        rest = None
    else:
        if resm:
            err = True
            log.error('Found M and value in ' + line)
            rest = None
            resb = 0
        elif line[firstval] == "'":
            rest = line[firstval + 1:-1]
            resb = 0
        else:
            rest = None
            resb, verr = check_int(line[firstval:],
                                   'Value in ' + line + ' ' + str(firstval))
            if verr:
                err = True
    if resb < 0 or resb > 255 or (resa and resb > 2):
        log.error('Value out of range in ' + line)
        resb = 0
        err = True

    tmpr = I2cOp(resr, resc, ress, resp, resn, resm, resa, 0, resb, rest)
    size, serr = check_and_size(tmpr, line)
    if serr:
        err = True
    return I2cOp(resr, resc, ress, resp, resn, resm, resa, size, resb,
                 rest), err


def parse_file(infile, fifodata=False, prefix=None):
    ''' Parse a file of I2C data
        fifodata indicates if the data is a dump from writes to FDATA fifo
        prefix is a prefix on valid lines and will be stripped
               lines without the prefix are ignored
        Returns list of I2cOps or str (for titles)
    '''
    transaction = []
    errors = 0
    firstline = True

    for line in infile:
        if prefix:
            if not line.startswith(prefix):
                continue
            line = line[len(prefix):]

        if len(line) == 0 or line.isspace() or line[0] == '#':
            continue
        line = line.lstrip().rstrip()
        if line[0] == 'T':
            transaction.append(line[1:].lstrip())
            continue
        schar = ','
        if fifodata and not ',' in line:
            # fifodata could also be whitespace spearated
            schar = None

        for sline in line.split(sep=schar):
            if fifodata:
                t, err = parse_i2c_fifodata(sline)
            else:
                t, err = parse_i2c_code(sline)
            if err:
                errors += 1
            else:
                transaction.append(t)
    if errors > 0:
        log.error('Found ' + str(errors) + ' errors in input')
    return transaction


def output_debug(outfile, t, term):
    for tr in t:
        outfile.write(str(tr) + term)


def text_element(tr, term, titles):
    if isinstance(tr, str):
        if titles:
            return 'T ' + tr + term
        return ''
    flags = 'S' if tr.start else '.'
    flags += 'P' if tr.stop else '.'
    flags += 'R' if tr.read else '.'
    flags += 'C' if tr.rcont else '.'
    flags += 'N' if tr.nackok else '.'

    # mvalue and adr are only for drawing, but can propagate in value
    if tr.adr:
        val = 'A' + str(tr.fbyte)
    else:
        if tr.tag:
            val = "'" + tr.tag + "'"
        else:
            val = 'M' if tr.mvalue else hex(tr.fbyte)
    return flags + ' ' + val + term


def output_text(outfile, transactions, term, titles=True):
    for tr in transactions:
        text = text_element(tr, term, titles)
        if text:
            outfile.write(text)


# use will place a defined group at the given x,y
def svg_use(item, x, y):
    return '    <use href="#' + item + '" x="' + str(x) + \
        '" y="' + str(y) + '" />\n'


# a byte write is a byte of data from the host and an ack from the device
def svg_wrbyte(xpos, ypos, nok, label):
    rtext = svg_use('hbyte', xpos, ypos)
    rtext += '    <text x="' + str(xpos + (sdata.bytew / 2))
    rtext += '" y="' + str(ypos + sdata.txty) + '">\n'
    rtext += label
    rtext += '</text>\n'
    xpos += sdata.bytew
    if nok:
        rtext += svg_use('norackd', xpos, ypos)
    else:
        rtext += svg_use('ackd', xpos, ypos)
    xpos += sdata.bitw
    return rtext, xpos


# a byte read is a byte of data from the device and an ack/nack from the host
def svg_rdbyte(xpos, ypos, ack, label):
    rtext = svg_use('dbyte', xpos, ypos)
    rtext += '    <text x="' + str(xpos + (sdata.bytew / 2))
    rtext += '" y="' + str(ypos + sdata.txty) + '">\n'
    rtext += label
    rtext += '</text>\n'
    xpos += sdata.bytew
    rtext += svg_use(ack, xpos, ypos)
    xpos += sdata.bitw
    return rtext, xpos


def svg_element(tr, xpos, ypos):
    etext = ''
    if tr.start:
        etext += svg_use('start', xpos, ypos)
        xpos += sdata.bitw

    if tr.read and not tr.mvalue:
        for n in range(0, 1 if tr.tag else tr.fbyte):
            acktype = 'ackh' if (n < tr.fbyte - 1) or tr.rcont else 'nackh'
            t, xpos = svg_rdbyte(xpos, ypos, acktype,
                                 tr.tag if tr.tag else 'D' + str(n + 1))
            etext += t
            if xpos > sdata.wrap and (n < tr.fbyte - 1):
                xpos = sdata.cindent
                ypos += sdata.linesep
    elif tr.read and tr.mvalue:
        # need space to draw three byte+ack and a break squiggle
        if (xpos + (sdata.bytew + sdata.bitw) * 3 + sdata.bitw) > sdata.wrap:
            xpos = sdata.cindent
            ypos += sdata.linesep
        t, xpos = svg_rdbyte(xpos, ypos, 'ackh', 'Data1')
        etext += t
        t, xpos = svg_rdbyte(xpos, ypos, 'ackh', 'Data2')
        etext += t
        etext += svg_use('skip', xpos, ypos)
        xpos += sdata.bitw
        t, xpos = svg_rdbyte(xpos, ypos, 'nackh', 'DataN')
        etext += t

    elif tr.adr:
        etext += svg_use('adr' + str(tr.fbyte), xpos, ypos)
        xpos += sdata.bytew
        etext += svg_use('ackd', xpos, ypos)
        xpos += sdata.bitw
    elif tr.mvalue:
        # need space to draw three byte+ack and a break squiggle
        if (xpos + (sdata.bytew + sdata.bitw) * 3 + sdata.bitw) > sdata.wrap:
            xpos = sdata.cindent
            ypos += sdata.linesep
        t, xpos = svg_wrbyte(xpos, ypos, tr.nackok, 'Data1')
        etext += t
        t, xpos = svg_wrbyte(xpos, ypos, tr.nackok, 'Data2')
        etext += t
        etext += svg_use('skip', xpos, ypos)
        xpos += sdata.bitw
        t, xpos = svg_wrbyte(xpos, ypos, tr.nackok, 'DataN')
        etext += t

    elif tr.start:  # and not tr.adr by position in elif
        etext += svg_use('adr' + str(tr.fbyte & 1), xpos, ypos)
        etext += '    <text x="' + str(xpos + 115)
        etext += '" y="' + str(ypos + sdata.txty) + '">' + hex(tr.fbyte >> 1)
        etext += '</text>\n'
        xpos += sdata.bytew
        etext += svg_use('ackd', xpos, ypos)
        xpos += sdata.bitw

    else:
        t, xpos = svg_wrbyte(xpos, ypos, tr.nackok,
                             tr.tag if tr.tag else hex(tr.fbyte))
        etext += t

    if tr.stop:
        etext += svg_use('pstop', xpos, ypos)
        xpos += sdata.bitw

    return etext, xpos, ypos


# since they are referenced by href name the style and defs only
# go in the first svg in a file
first_svg = True


def out_svg(outfile, svg, ypos, svgtext):
    global first_svg
    outfile.write('<svg\n' + sdata.svgtag_consts)
    outfile.write('viewBox="0 0 ' + str(sdata.svgw) + ' ' +
                  str(ypos + sdata.linesep + 8) + '">\n')
    if (first_svg):
        outfile.write(sdata.svgstyle + sdata.svg_defs)
        first_svg = False
    outfile.write(svg)
    if svgtext:
        outfile.write('<text x="10" y="' + str(ypos + sdata.linesep + 3))
        outfile.write('" class="tt">' + svgtext[:-2] + '</text>\n')
    outfile.write('</svg>\n')


def output_svg(outfile, transactions, title):
    xpos = 0
    ypos = 0
    svg = ''
    svgtext = ''
    for tr in transactions:
        if isinstance(tr, str):
            if svg:
                out_svg(outfile, svg, ypos, svgtext)
            if title:
                outfile.write('<h2>' + tr + '</h2>\n')
            xpos = 0
            ypos = 0
            svg = ''
            svgtext = ''
            continue
        if xpos > sdata.wrap:
            xpos = sdata.cindent
            ypos += sdata.linesep
        trsvg, xpos, ypos = svg_element(tr, xpos, ypos)
        svgtext += text_element(tr, ', ', False)
        svg += trsvg

    out_svg(outfile, svg, ypos, svgtext)
