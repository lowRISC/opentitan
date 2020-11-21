#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Script to convert logs placed in given sections into SystemVerilog-friendly
database.

The tool uses the pyelftools utility to extract the log fields from a given
section and the strings from read only sections. It processes the log fields
& the strings and converts them into a database. The script produces 2 outputs:
- <name_logs.txt, which is the log database
- <name>_rodata.txt which contains {addr: string} pairs.
"""

import argparse
import os
import re
import struct
import sys

from elftools.elf import elffile

# A printf statement in C code is converted into a single write to a reserved
# address in the RAM. The value written is the address of the log_fields_t
# struct constucted from the log. It has the following fields:
# severity (int), 4 bytes:        0 (I), 1 (W), 2 (E), 3 (F)
# file_name (int, ptr), 4 bytes:  Pointer to file_name string.
# Line no (int), 4 bytes:         Line number of the log message.
# Nargs (int), 4 bytes:           Number of arguments the format string takes.
# format (int, ptr), 4 bytes:     Log format string.
#
# Total size of log_fields_t: 20 bytes.
LOGS_FIELDS_SECTION = '.logs.fields'
LOGS_FIELDS_SIZE = 20
RODATA_SECTION = '.rodata'


def cleanup_newlines(string):
    '''Replaces newlines with a carriage return.

    The reason for doing so if a newline is encountered in the middle of a
    string, it ends up adding that newline in the output files this script
    generates. The output of this script is consumed by a monitor written in
    SystemVerilog (hw/dv/sv/sw_logger_if), a language with limited parsing
    / processing capability. So we make the parsing easier on the SV side by
    putting all multiline strings on a single line, separated by a single
    carriage return instead, which the SV monitor can easily replace with
    a newline.'''
    return re.sub(r"[\n\r]+", "\r", string).strip()


def cleanup_format(_format):
    '''Converts C style format specifiers to SV style.

    It makes the folllowing substitutions:
    - Change %[N]?i, %[N]?u --> %[N]?d
    - Change %[N]?x, %[N]?p --> %[N]?h
    - Change %[N]?X         --> %[N]?H

    The below is a non-standard format specifier added in OpenTitan
    (see sw/device/lib/base/print.c for more details). A single %z specifier
    consumes 2 arguments instead of 1 and hence has to converted as such to
    prevent the log monitor in SystemVerilog from throwing an error at runtime.
    - Change %[N]?z         --> %[N]?s[%d].'''
    _format = re.sub(r"(%-?\d*)[iu]", r"\1d", _format)
    _format = re.sub(r"(%-?\d*)[xp]", r"\1h", _format)
    _format = re.sub(r"(%-?\d*)X", r"\1H", _format)
    _format = re.sub(r"(%-?\d*)z", r"\1s[%d]", _format)
    _format = re.sub(r"%([bcodhHs])", r"%0\1", _format)
    return cleanup_newlines(_format)


def get_string_format_specifier_indices(_format):
    '''Returns the indices of string format specifiers %s in the format string.

    Example: a = %d, %%b = %%%2c, %%%% c = %5s, %% d = %o, e = %x, f = %-1s
    The function will return: `2 5` because the 2nd and the 5th arg to the
    format are strings. The '%%' does not accept an arg so they are ignored.
    The returned value is a string of indices separated by a single space.

    It is assumed that _format has been passed through `cleanup_format()`.
    '''
    pattern = '''
         %                    # literal "%"
         (?:[-+0 #]{0,5})     # optional flags
         (?:\d+|\*)?          # width
         (?:\.(?:\d+|\*))?    # precision
         (?:l|ll)?            # size
         ([cdiouxpXshH])      # type (returned if matched)
         |                    # OR
         %(%)                 # literal "%%" (returned if matched)
         '''
    m = re.findall(pattern, _format, re.X)
    # With the above example, the output of the pattern match is:
    # [('d', ''), ('', '%'), ('', '%'), ('c', ''), and so on..]
    index = 0
    result = []
    for match in m:
        if match[1] == '%': continue
        if match[0] == 's': result.append(str(index))
        index += 1
    return ' '.join(result).strip()


def prune_filename(filename):
    'This function prunes the filename to only display the hierarchy under sw/'
    hier = "sw/device"
    index = filename.find(hier)
    return (filename if index == -1 else filename[index:])


def get_addr_strings(ro_contents):
    '''Construct {addr: string} dict from all read-only sections.

    This function processes the read-only sections of the elf supplied as
    a list of ro_content tuples comprising of base addr, size and data in bytes
    and converts it into an {addr: string} dict which is returned.'''
    result = {}
    for ro_content in ro_contents:
        str_start = 0
        base_addr, size, data = ro_content
        while (str_start < size):
            str_end = data.find(b'\0', str_start)
            # Skip if start and end is the same
            if str_start == str_end:
                str_start += 1
                continue
            # Get full string address by adding base addr to the start.
            addr = base_addr + str_start
            string = cleanup_newlines(data[str_start:str_end].decode(
                'utf-8', errors='replace'))
            if addr in result:
                exc_msg = "Error: duplicate {addr: string} pair encountered\n"
                exc_msg += "addr: {} string: {}\n".format(addr, result[addr])
                exc_msg += "addr: {} string: {}\n".format(addr, string)
                raise IndexError(exc_msg)
            result[addr] = string
            str_start = str_end + 1
    return result


def get_str_at_addr(str_addr, addr_strings):
    '''Returns the string at the provided addr.

    It may be possible that the input addr is an offset within the string.
    If true, then it returns remainder of the string starting at the offset.'''
    for addr in addr_strings.keys():
        if addr <= str_addr < addr + len(addr_strings[addr]):
            return addr_strings[addr][str_addr - addr:].strip()
    raise KeyError("string at addr {} not found".format(str_addr))


def extract_sw_logs(elf_file, logs_fields_section, ro_sections):
    '''This function extracts contents from the logs fields section, and the
    read only sections, processes them and generates a tuple of (results) -
    log with fields and (rodata) - constant strings with their addresses.
    '''
    # Open the elf file.
    with open(elf_file, 'rb') as f:
        elf = elffile.ELFFile(f)
        # Parse the ro sections to get {addr: string} pairs.
        ro_contents = []
        for ro_section in ro_sections:
            section = elf.get_section_by_name(name=ro_section)
            if section:
                base_addr = int(section.header['sh_addr'])
                size = int(section.header['sh_size'])
                data = section.data()
                ro_contents.append((base_addr, size, data))
            else:
                print("Error: {} section not found in {}".format(
                    ro_section, elf_file))
                sys.exit(1)
        addr_strings = get_addr_strings(ro_contents)

        # Dump the {addr: string} data.
        rodata = ""
        for addr in addr_strings.keys():
            rodata += "addr: {}\n".format(hex(addr)[2:])
            string = cleanup_newlines(addr_strings[addr])
            rodata += "string: {}\n".format(string)

        # Parse the logs fields section to extract the logs.
        section = elf.get_section_by_name(name=logs_fields_section)
        if section:
            logs_base_addr = int(section.header['sh_addr'])
            logs_size = int(section.header['sh_size'])
            logs_data = section.data()
        else:
            print("Error: {} section not found in {}".format(
                logs_fields_section, elf_file))
            sys.exit(1)

        # Dump the logs with fields.
        result = ""
        num_logs = logs_size // LOGS_FIELDS_SIZE
        for i in range(num_logs):
            start = i * LOGS_FIELDS_SIZE
            end = start + LOGS_FIELDS_SIZE
            severity, file_addr, line, nargs, format_addr = struct.unpack(
                'IIIII', logs_data[start:end])
            result += "addr: {}\n".format(hex(logs_base_addr + start)[2:])
            result += "severity: {}\n".format(severity)
            result += "file: {}\n".format(
                prune_filename(get_str_at_addr(file_addr, addr_strings)))
            result += "line: {}\n".format(line)
            result += "nargs: {}\n".format(nargs)
            fmt = cleanup_format(get_str_at_addr(format_addr, addr_strings))
            result += "format: {}\n".format(fmt)
            result += "str_arg_idx: {}\n".format(
                get_string_format_specifier_indices(fmt))

        return rodata, result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--elf-file', '-e', required=True, help="Elf file")
    parser.add_argument('--logs-fields-section',
                        '-f',
                        default=LOGS_FIELDS_SECTION,
                        help="Elf section where log fields are written.")
    parser.add_argument('--rodata-sections',
                        '-r',
                        nargs="+",
                        action="append",
                        help="Elf sections with rodata.")
    parser.add_argument('--name',
                        '-n',
                        required=True,
                        help="Type of the SW elf being processed.")
    parser.add_argument('--outdir',
                        '-o',
                        required=True,
                        help="Output directory.")
    args = parser.parse_args()

    if args.rodata_sections is None:
        ro_sections = [RODATA_SECTION]
    else:
        # TODO: We want the `--rodata-sections` arg to have the 'extend' action
        # which is only available in Python 3.8. To maintain compatibility with
        # Python 3.6 (which is the minimum required version for OpenTitan), we
        # flatten the list here instead.
        ro_sections = list(
            set([section for lst in args.rodata_sections for section in lst]))

    os.makedirs(args.outdir, exist_ok=True)
    rodata, result = extract_sw_logs(args.elf_file, args.logs_fields_section,
                                     ro_sections)

    outfile = os.path.join(args.outdir, args.name + ".rodata.txt")
    with open(outfile, "w", encoding='utf-8') as f:
        f.write(rodata.strip())

    outfile = os.path.join(args.outdir, args.name + ".logs.txt")
    with open(outfile, "w", encoding='utf-8') as f:
        f.write(result.strip())


if __name__ == "__main__":
    main()
