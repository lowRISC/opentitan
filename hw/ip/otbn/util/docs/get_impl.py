# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional, Sequence

import libcst as cst


class ImplVisitor(cst.CSTVisitor):
    '''An AST visitor used to extract documentation from the ISS'''
    def __init__(self) -> None:
        self.impls = {}  # type: Dict[str, Sequence[cst.BaseStatement]]

        self.cur_class = None  # type: Optional[str]

    def visit_ClassDef(self, node: cst.ClassDef) -> None:
        assert self.cur_class is None
        self.cur_class = node.name.value

    def leave_ClassDef(self, node: cst.ClassDef) -> None:
        self.cur_class = None

    def leave_FunctionDef(self, node: cst.FunctionDef) -> None:
        if ((self.cur_class is None or
             node.name.value != 'execute' or
             self.cur_class in self.impls)):
            return

        # The body of a function definition is always an IndentedBlock. Strip
        # that out to get at the statements inside.
        assert isinstance(node.body, cst.IndentedBlock)
        self.impls[self.cur_class] = node.body.body


def read_implementation(path: str) -> Dict[str, str]:
    '''Read the implementation at path (probably insn.py)

    Returns a dictionary from instruction class name to its pseudo-code
    implementation. An instruction class name looks like ADDI (for addi) or
    BNADDM (for bn.addm).

    '''
    with open(path, 'r') as handle:
        node = cst.parse_module(handle.read())

    # Extract the function bodies
    visitor = ImplVisitor()
    node.visit(visitor)

    # Render the function bodies
    return {cls: ''.join(node.code_for_node(stmt) for stmt in body)
            for cls, body in visitor.impls.items()}
