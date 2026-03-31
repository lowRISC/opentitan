#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import logging as log
import sys
import re
from pathlib import Path

"""
Generate several files for the relocatable or binary blob compilation.

Create a jump table by parsing the public header files and keeping functions
that are specify in a configuration file.

Output files:
  <prefix>_jump_table.c: jump table containing the array of function pointers
  <prefix>_jump_table.h: define index for the jump table
  <prefix>_lib_parser.c (only for binary blob): wrapper for public functions which
    retrieve the function in a binary blob by parsing the jump table.
  <prefix>_linker_script.ld: script to use to generate an executable for the binary blob
    or for the relocatable library.
"""


def normalize_public_header(out_dir, headers):
    """
    Normalize the headers file by removing the comments, the pre-processing
    commands and attribute and provide the function in one-line with the
    following format:
    <return_type> <function_name>(<arg list>);
    """
    normalized_header = []
    for header in headers:
        with open(header, "r") as h:
            content = h.read()
        # Remove extra space at start or end
        content = re.sub(r"^\s+", "", content, flags=re.MULTILINE)
        content = re.sub(r"\s+$", "", content, flags=re.MULTILINE)
        # Remove comments (// and /**/ style)
        content = re.sub(r"/\*.*?\*/", "", content, flags=re.DOTALL)
        content = re.sub(r"//.*?$", "", content, flags=re.MULTILINE)
        # Remove pre-processing command
        #   Remove line starting with #
        content = re.sub(r"^#.*?$", "", content, flags=re.MULTILINE)
        #   Remove multi-line preprocessor (line finishing by \ and the last line
        #   after \)
        content = re.sub(r"^.*\\.*\n.*?[^\\]$", "", content, flags=re.MULTILINE)
        content = re.sub(r"^.*\\.*$", "", content, flags=re.MULTILINE)
        # Remove attribute
        content = re.sub(r"__attribute__\(\(.*?\)\)", "", content)
        # One line function: add line return only after ;
        content = re.sub(r"\n", " ", content)
        content = re.sub(r";", ";\n", content)
        # Remove space at start and end
        content = re.sub(r"^\s+", "", content, flags=re.MULTILINE)
        content = re.sub(r"\s+$", "", content, flags=re.MULTILINE)
        # Remove extern key word
        content = re.sub(r"^extern ", "", content, flags=re.MULTILINE)

        content = content.split("\n")

        normalized_header += content

    return normalized_header


def remove_unused_functions(out_dir, normalized_header, config_file):
    """
    Remove from a normalized header the function that are not part of the
    config_file.
    Config_file contains a list of the function names to be kept.
    Normalized_header contains a list of functions declaration of the following
    format: <return_type> <function_name>(<arg list>);
    """
    stripped_header = []
    with open(config_file, "r") as config:
        names = config.readlines()
        names = [name.strip() for name in names]

    for function in normalized_header:
        # Keep only the name of the function
        fun_name = function.split(" ", 1)
        if len(fun_name) < 2:
            continue
        fun_name = fun_name[1].split("(", 1)[0]
        if fun_name in names:
            stripped_header.append(function)

    return stripped_header


def generate_jump_table(out_dir, prefix, stripped_header, headers):
    """
    Generate
    - <prefix>_jump_table.c: contains a metadata structure, a hash array and
    a vector table that is generated from the stripped header;
    - <prefix>_jump_table.h: contains the structure definition for the metadata and
      an enumeration for the index of the function in the jump table
    """
    banner = "/* This is a generated file. DO NOT MODIFY. */\n"
    include_c = f'#include "{prefix}_jump_table.h"\n'
    for header in headers:
        include_c += f'#include "{header}"\n'

    header_c = """
__attribute__((used)) __attribute__((section(".metadata")))
const header_t metadata = {
  .version = 1,
  .magic = 0x70797263,
};

__attribute__((used)) __attribute__((section(".libotcrypto_hash")))
const uint8_t sha384_hash[48] = {0};

__attribute__((used)) __attribute__((section(".jump_table")))
const void *jump_table[] = {
"""

    footer_c = """
};

"""

    header_h = """
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_JUMP_TABLE_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_JUMP_TABLE_H_

#include "sw/device/lib/crypto/include/otcrypto.h"

typedef struct {
  uint32_t version;
  uint32_t magic;
} header_t;

enum {
"""
    footer_h = """
};

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_JUMP_TABLE_H_
"""
    jump_table_c = f"{out_dir}/{prefix}_jump_table.c"
    jump_table_h = f"{out_dir}/{prefix}_jump_table.h"
    with open(jump_table_c, "w") as c_file, open(jump_table_h, "w") as h_file:
        c_file.write(banner)
        c_file.write(include_c)
        c_file.write(header_c)
        h_file.write(banner)
        h_file.write(header_h)
        for function in stripped_header:
            # Get the name of the function
            name = function.split(" ", 1)
            if len(name) < 2:
                continue
            name = name[1].split("(", 1)[0]
            # Upper case the name and add _IDX
            idx = name.upper() + "_IDX"
            c_file.write(f"    [{idx}] = {name},\n")
            h_file.write(f"    {idx},\n")

        c_file.write(footer_c)
        h_file.write(footer_h)


def generate_linker_script(out_dir, prefix, address):
    """
    Generate linker script used for binary blob creation.
    In case of PIC code the origin address should be 0
    """
    banner = "/* This is a generated file. DO NOT MODIFY */\n"
    memory = f"MEMORY {{ ROM (RX): ORIGIN = {address}, LENGTH = 256K }}\n"

    section = """
SECTIONS
{
    .metadata : {
        _libotcrypto_start_ = .;
          KEEP(*(.metadata))
    } > ROM

    .jump_table : {
        KEEP(*(.jump_table))
    } > ROM

    .text : {
        KEEP(*(.text))
        *(.text*)
        KEEP(*(.rodata*))
        _libotcrypto_end_ = .;
        _libotcrypto_hash_ = .;
        KEEP(*(.libotcrypto_hash*))
    } > ROM  = 0xffffffff

    .data : {
        *(.data*);
        *(.sdata*);
    } > ROM
    ASSERT(SIZEOF(.data) == 0, "No .data data allowed")

    .bss : {
        *(.bss*);
        *(.sbss*);
    } > ROM
    ASSERT(SIZEOF(.bss) == 0, "No .bss data allowed")

    .got : {
        *(.got*)
        *(.plt*)
        *(.iplt*)
    }
    ASSERT(SIZEOF(.got) == 0, "No .got allowed")

    .rela : {
        *(.rela*)
        *(.rel*)
    }
    ASSERT(SIZEOF(.rela) == 0, "No relocations allowed")
}
"""
    linker_script = f"{out_dir}/{prefix}_linker_script.ld"
    with open(linker_script, "w") as f:
        f.write(banner)
        f.write(memory)
        f.write(section)


def generate_lib_parser_c(out_dir, prefix, stripped_header, pic, headers):
    """
    Generate function wrapper {prefix}_lib_parser.c that is needed for
    the binary blob parsing.
    The way the address of the functions is computed inside the binary blob
    is different if the code is position-independent or position-dependent.
    """
    banner = "/* This is a generated file. DO NOT MODIFY */\n"
    include = f'#include "{prefix}_jump_table.h"\n'
    for header in headers:
        include += f'#include "{header}"\n'

    header = """
#define JUMP_TABLE_START (sizeof(header_t))
extern uint8_t blob[];

"""
    lib_parser_c = f"{out_dir}/{prefix}_lib_parser.c"
    with open(lib_parser_c, "w") as file:
        file.write(banner)
        file.write(include)
        file.write(header)

        for function in stripped_header:
            # Get the name of the function
            name = function.split(" ", 1)
            if len(name) < 2:
                continue
            name = name[1].split("(", 1)[0]
            # Create the idx name of the function
            idx = name.upper() + "_IDX"

            # Typedef for the function
            type_name = name + "_t"
            # Create a typedef for every function of the following format:
            # typedef <return_type> (*<function_name>_t)(<arg_list>);
            typedef = re.sub(r"^(\w+\s+)(\w+)(\(.*)$", r"typedef \1(*\2_t)\3", function)

            # Get the list of arguments without there type by selecting the word
            # that come before the comma or before the closing bracket
            # Resulting format: arg1, arg2, arg3)
            argument = re.findall(r"\w+\s*\[?[0-9]*?\]?[,\)]", function)
            # Some arguments are provided as array, in that case remove the array
            # brackets
            argument = [re.sub(r"\[[0-9]*\]", "", arg) for arg in argument]
            argument = " ".join(argument)
            # Remove void if the list of arguments is empty
            argument = re.sub(r"void", "", argument)

            file.write(f"{typedef}\n")
            function = re.sub(r";", "{", function)
            file.write(f"{function}\n")
            file.write(
                f"    uint32_t *blob_addr = \
                    (uint32_t *)(&blob[JUMP_TABLE_START + {idx} * sizeof(void *)]);\n"
            )

            if pic:
                file.write(
                    f"    {type_name} fun = \
                        ({type_name})((uintptr_t)*blob_addr + (uintptr_t)blob);\n"
                )
            else:
                file.write(
                    f"    {type_name} fun = ({type_name})((uintptr_t)*blob_addr);\n"
                )

            file.write(f"    return fun({argument};\n")
            file.write("}\n\n")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--out-dir",
        "-o",
        required=False,
        default=".",
        help="Output directory (default: %(default)s)",
    )
    parser.add_argument(
        "--config",
        "-c",
        required=False,
        default="",
        help="File containing the functions to keep for the given config option",
    )
    parser.add_argument(
        "--binary_blob",
        "-b",
        required=False,
        action="store_true",
        help="Indicate to generate files for the binary blob compilation.",
    )
    parser.add_argument(
        "--prefix",
        "-r",
        required=True,
        help="Prefix for the name of the generated files.",
    )
    parser.add_argument(
        "--pic",
        "-p",
        required=False,
        action="store_true",
        help="Indicate that the code is position-independent.",
    )
    parser.add_argument(
        "--address",
        "-a",
        required=True,
        help="Address in memory for the linker script (0 for pic)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true", help="Print commands that are executed."
    )
    parser.add_argument("headers", nargs="+", type=str, metavar="SRC_FILE")
    args = parser.parse_args()

    log_level = log.INFO if args.verbose else log.WARNING
    log.basicConfig(level=log_level, format="%(message)s")

    if args.pic and (args.address != "0"):
        log.fatal("Invalid parameters: linker address should be 0 for pic")
        return 1

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    headers = [Path(f) for f in args.headers]
    for header in headers:
        if not header.exists():
            log.fatal("Header file %s not found." % header)
            return 1

    if args.config:
        config = Path(args.config)
        if not config.exists():
            log.fatal("Config file %s not found." % config)
            return 1

    generate_linker_script(out_dir, args.prefix, args.address)

    # Keep only functions declaration from the header files
    normalized_header = normalize_public_header(out_dir, headers)

    # Remove unused functions
    if args.config:
        stripped_header = remove_unused_functions(
            out_dir, normalized_header, Path(args.config)
        )
    else:
        stripped_header = normalized_header

    # Generate jump_table.h and jump_table.c
    generate_jump_table(out_dir, args.prefix, stripped_header, headers)

    # Generate lib_parser.c for binary blob compilation
    if args.binary_blob:
        generate_lib_parser_c(out_dir, args.prefix, stripped_header, args.pic, headers)

    return 0


if __name__ == "__main__":
    sys.exit(main())
