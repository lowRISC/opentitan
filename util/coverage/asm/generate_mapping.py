#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Emit LLVM coverage mapping data."""

import argparse
import textwrap

from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from util.coverage.asm.basic_block import (
    flatten_blocks,
    propagate_counter,
    run_analyze_pipeline,
    set_statement_counter,
)
from util.coverage.asm.encoding import (
    encode_filepath,
    encode_oct,
    encode_prf_names,
    encode_regions,
    get_hash,
)
from util.coverage.asm.tokenizer import (
    Statement,
    StmtType,
    run_tokenize_pipeline,
)


def collect_functions(
    statements: List[Statement],
) -> Tuple[Dict[str, List[Statement]], List[Statement]]:
    """Collects function names and groups statements into functions.

    Statements not assigned to any function are grouped into `global_code`.

    Args:
        statements: A list of `Statement` objects representing assembly
          statements.

    Returns:
        A tuple containing:
        - A dictionary where keys are function names (str) and values are lists
          of `Statement` objects belonging to that function.
        - A list of `Statement` objects that do not belong to any specific
        function.
    """
    # Collect function names
    func_names: Set[str] = set()
    for stmt in statements:
        if stmt.type == StmtType.FUNCTYPE:
            func_names.add(stmt.args.strip())

    # Group statements into functions.
    # Statements not assigned to any function are grouped into global_code.
    global_code: List[Statement] = []
    current_func: Optional[str] = None
    functions: Dict[str, List[Statement]] = {}
    for stmt in statements:
        if stmt.type == StmtType.LABEL and stmt.args in func_names:
            if current_func is not None:
                raise NotImplementedError(
                    'Overlapped function is not supported'
                )
            current_func = stmt.args.strip()
            functions[current_func] = []

        if current_func is not None:
            functions[current_func].append(stmt)
        else:
            global_code.append(stmt)

        if stmt.type == StmtType.FUNCEND and stmt.args == current_func:
            assert (
                stmt.block_counter is None
            ), 'Function end directive should not be reachable'
            current_func = None

    return functions, global_code


def get_counter_section(statements: List[Statement]) -> str:
    """Extracts the coverage counter section name from statements.

    Args:
        statements: A list of `Statement` objects.

    Returns:
        The name of the counter section.

    Raises:
        AssertionError: If the coverage counter section pragma is not specified
                        exactly once, or if the section name is empty.
    """
    counter_sections = [
        stmt
        for stmt in statements
        if stmt.type == StmtType.PRAGMA and stmt.mnemonic == 'section'
    ]
    assert (
        len(counter_sections) == 1
    ), 'Coverage counter section pragma should be specified once'
    counter_section: str = counter_sections[0].args.strip()
    assert counter_section, 'Counter section should not be empty'
    return counter_section


def get_max_counter(statements: List[Statement]) -> int:
    """Calculates the maximum counter value among all COUNTER statements.

    Args:
        statements: A list of `Statement` objects.

    Returns:
        The maximum counter value.
    """
    return max(s.counter for s in statements if s.type == StmtType.COUNTER)


def main(args: argparse.Namespace) -> None:
    """Main function to generate LLVM coverage mapping data.

    Args:
        args: An argparse.Namespace object containing command-line arguments.
          Expected arguments: - input: A list of Path objects for input ASM
          files. - output: A list of Path objects for output ASM files.
    """
    assert (
        len(args.input) == len(args.output)
    ), 'Number of inputs and outputs should be matched'

    for inp, out in zip(args.input, args.output):
        statements = run_tokenize_pipeline(inp.read_text())
        blocks = run_analyze_pipeline(statements)
        blocks = propagate_counter(blocks)
        blocks = set_statement_counter(blocks)

        statements = flatten_blocks(blocks)

        counter_section = get_counter_section(statements)
        counter_size = get_max_counter(statements) + 1

        covmap = encode_filepath(inp)
        covmap_hash = get_hash(covmap)
        unique_name = f'{inp.stem}_{covmap_hash:016X}u'

        functions, global_code = collect_functions(statements)
        if not all(stmt.is_comment for stmt in global_code):
            print('WARN: Some instructions are not assigned to a function.')
            functions[unique_name] = global_code

        prf_names: bytes = encode_prf_names(list(functions.keys()))

        # The structures are related to the compiler version and may require
        # updates if the compiler changes. These templates are adapted from
        # the assembly output of `clang` when compiling a simple C file with
        # coverage instrumentation enabled.
        #
        # $ /path/to/lowrisc/toolchain/clang -S test.c \
        #     -fprofile-instr-generate -fcoverage-mapping \
        #     -mllvm --enable-single-byte-coverage \
        with open(out, 'w') as outfile:
            # output original text, then append llvm covmap data.
            outfile.write(inp.read_text())

            # https://llvm.org/docs/InstrProfileFormat.html#names
            # Counters are shared between all functions.
            outfile.write(textwrap.dedent(f"""
                .type    .L__asm_profc,@object
                .section {counter_section},"aGw",@progbits,__asm_profc_{unique_name}
            .L__asm_profc:
                .zero    {counter_size}, 255
                .size    .L__asm_profc, {counter_size}
            """))

            # https://llvm.org/docs/InstrProfileFormat.html#names
            outfile.write(textwrap.dedent(f"""
                .type    .L__llvm_prf_nm,@object
                .section __llvm_prf_names,"aR",@progbits
            .L__llvm_prf_nm:
                .ascii   {encode_oct(prf_names)}
                .size    .L__llvm_prf_nm, {len(prf_names)}
            """))

            # https://llvm.org/docs/CoverageMappingFormat.html#coverage-mapping-header
            outfile.write(textwrap.dedent(f"""
                .type    .L__llvm_coverage_mapping,@object
                .section __llvm_covmap,"R",@progbits
                .p2align 3, 0x0
            .L__llvm_coverage_mapping:
                .word    0  /* Always zero */
                .word    {len(covmap)}
                .word    0  /* Always zero */
                .word    5  /* Coverage mapping format version */
                .ascii   {encode_oct(covmap)}
                .size    .L__llvm_coverage_mapping, {len(covmap) + 16}
            """))

            for name, func_statements in functions.items():
                name_hash = get_hash(name.encode())

                covrec = encode_regions(func_statements)

                # https://llvm.org/docs/InstrProfileFormat.html#profile-metadata
                outfile.write(textwrap.dedent(f"""
                /* Function {name} */
                    .type    .L__asm_profd_{name},@object
                    .section __llvm_prf_data,"aGw",@progbits,__asm_profc_{unique_name}
                    .p2align 3
                .L__asm_profd_{name}:
                    .quad    0x{name_hash:016X}
                    .quad    31337  /* Fake structural hash */
                    .word    .L__asm_profc - .L__asm_profd_{name}
                    .word    0
                    .word    0
                    .word    {counter_size}
                    .zero    4
                    .zero    4
                    .size    .L__asm_profd_{name}, 40
                """))

                # https://llvm.org/docs/CoverageMappingFormat.html#function-record
                outfile.write(textwrap.dedent(f"""
                    .hidden  __covrec_{name_hash:016X}u
                    .type    __covrec_{name_hash:016X}u,@object
                    .section __llvm_covfun,"GR",@progbits,__covrec_{name_hash:016X}u,comdat
                    .weak    __covrec_{name_hash:016X}u
                    .p2align 3, 0x0
                __covrec_{name_hash:016X}u:
                    .quad    0x{name_hash:016X}
                    .word    {len(covrec)}
                    .quad    31337  /* Fake structural hash */
                    .quad    0x{covmap_hash:016X}
                    .ascii   {encode_oct(covrec)}
                    .size    __covrec_{name_hash:016X}u, {len(covrec) + 28}
                """))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Emit LLVM coverage mapping data.'
    )
    parser.add_argument(
        '--input',
        nargs='+',
        type=Path,
        help='Input ASM file(s) to be processed.',
    )
    parser.add_argument(
        '--output',
        nargs='+',
        type=Path,
        help='Output ASM file(s) with coverage mapping appended.',
    )
    args = parser.parse_args()
    main(args)
