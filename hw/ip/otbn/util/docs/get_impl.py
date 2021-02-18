# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional, Sequence

import libcst as cst
from libcst._nodes.internal import CodegenState


class RegRef(cst.Subscript):
    '''An expression class to represent references to the register file'''
    gprs = cst.Name('GPRs')
    wdrs = cst.Name('WDRs')

    is_wide: bool
    idx: cst.BaseExpression

    def __init__(self, is_wide: bool, idx: cst.BaseExpression):
        # We want to do a computation when defining the fields in the base
        # class (value and slice). That means we can't use the automatically
        # generated init method from dataclass (nor can we use it's
        # __post_init__ hook: that would happen too late).
        #
        # However, we also want to store fields ourselves (is_wide and idx). We
        # can't just do something like "self.is_wide = is_wide", because that
        # crashes into the frozen setattr that the base class defines. Instead,
        # we have to use object.__setattr__ directly.
        sub_elt = cst.SubscriptElement(slice=cst.Index(value=idx))
        super().__init__(value=(RegRef.wdrs if is_wide else RegRef.gprs),
                         slice=[sub_elt])
        object.__setattr__(self, 'is_wide', is_wide)
        object.__setattr__(self, 'idx', idx)

    def _visit_and_replace_children(self,
                                    visitor: cst.CSTVisitorT) -> 'RegRef':
        new_idx = self.idx.visit(visitor)
        if isinstance(new_idx, cst.RemovalSentinel):
            raise ValueError('Cannot remove index of a RegRef')
        return RegRef(self.is_wide, new_idx)

    def _codegen_impl(self, state: CodegenState) -> None:
        reg_bank = 'WDRs' if self.is_wide else 'GPRs'
        state.add_token(reg_bank)
        state.add_token('[')
        with state.record_syntactic_position(self):
            self.idx._codegen(state)
        state.add_token(']')


class ImplTransformer(cst.CSTTransformer):
    '''An AST visitor used to extract documentation from the ISS'''
    def __init__(self) -> None:
        self.impls = {}  # type: Dict[str, Sequence[cst.BaseStatement]]

        self.cur_class = None  # type: Optional[str]

    def visit_ClassDef(self, node: cst.ClassDef) -> Optional[bool]:
        assert self.cur_class is None
        self.cur_class = node.name.value
        return None

    def leave_ClassDef(self,
                       orig: cst.ClassDef,
                       updated: cst.ClassDef) -> cst.BaseStatement:
        self.cur_class = None
        return updated

    def leave_FunctionDef(self,
                          orig: cst.FunctionDef,
                          updated: cst.FunctionDef) -> cst.BaseStatement:
        if ((self.cur_class is None or
             updated.name.value != 'execute' or
             self.cur_class in self.impls)):
            return updated

        # The body of a function definition is always an IndentedBlock. Strip
        # that out to get at the statements inside.
        assert isinstance(updated.body, cst.IndentedBlock)
        self.impls[self.cur_class] = updated.body.body
        return updated

    @staticmethod
    def match_get_reg(call: cst.BaseExpression) -> Optional[RegRef]:
        '''Extract a RegRef from state.gprs.get_reg(foo)

        Returns None if this isn't a match.

        '''
        if not isinstance(call, cst.Call):
            return None

        # We expect a single argument (which we take as the index)
        if len(call.args) != 1:
            return None

        getreg_idx = call.args[0].value

        # All we need to do still is check that call.func is an
        # attribute representing state.gprs.get_reg or state.wdrs.get_reg.
        if ((not isinstance(call.func, cst.Attribute) or
             call.func.attr.value != 'get_reg')):
            return None

        state_dot_reg = call.func.value
        if not isinstance(state_dot_reg, cst.Attribute):
            return None

        # Finally, state_dot_reg should be either state.gprs or state.wdrs
        if not (isinstance(state_dot_reg.value, cst.Name) and
                state_dot_reg.value.value == 'state'):
            return None

        regfile_name = state_dot_reg.attr.value
        if regfile_name == 'gprs':
            is_wide = False
        elif regfile_name == 'wdrs':
            is_wide = True
        else:
            return None

        return RegRef(is_wide, getreg_idx)

    def leave_Call(self,
                   orig: cst.Call,
                   updated: cst.Call) -> cst.BaseExpression:
        # Detect
        #
        #    state.gprs.get_reg(FOO).read_unsigned()
        #    state.gprs.get_reg(FOO).read_signed()
        #
        # and replace it with the expressions
        #
        #    GPRs[FOO]
        #    from_2s_complement(GPRs[FOO])
        #
        # respectively.

        # In either case, we expect updated.func to be some long attribute
        # (representing state.gprs.get_reg(FOO).read_X). For unsigned or
        # signed, we can check that it is indeed an Attribute and that
        # updated.args is empty (neither function takes arguments).
        if updated.args or not isinstance(updated.func, cst.Attribute):
            return updated

        # Now, check whether we're calling one of the functions we're
        # interested in.
        if updated.func.attr.value == 'read_signed':
            signed = True
        elif updated.func.attr.value == 'read_unsigned':
            signed = False
        else:
            return updated

        # Check that updated.func.value really does represent something of the
        # form "state.gprs.get_reg(FOO)".
        ret = ImplTransformer.match_get_reg(updated.func.value)
        if ret is None:
            return updated

        if signed:
            # If this is a call to read_signed, we want to wrap the returned
            # value in a call to a fake sign decode function.
            return cst.Call(func=cst.Name('from_2s_complement'),
                            args=[cst.Arg(value=ret)])
        else:
            return ret

    def leave_Expr(self,
                   orig: cst.Expr,
                   updated: cst.Expr) -> cst.BaseSmallStatement:
        # This is called when leaving statements that are just expressions. We
        # use it to spot
        #
        #   state.gprs.get_reg(foo).write_unsigned(bar)
        #   state.gprs.get_reg(foo).write_signed(bar)
        #
        # and turn it into
        #
        #   GPRs[FOO] = bar
        #   GPRs[FOO] = to_2s_complement(bar)

        if not isinstance(updated.value, cst.Call):
            return updated

        call = updated.value
        if len(call.args) != 1 or not isinstance(call.func, cst.Attribute):
            return updated

        value = call.args[0].value

        if call.func.attr.value == 'write_unsigned':
            rhs = value
        elif call.func.attr.value == 'write_signed':
            rhs = cst.Call(func=cst.Name('to_2s_complement'),
                           args=[cst.Arg(value=value)])
        else:
            return updated

        # We expect call.func.value to be match state.gprs.get_reg(foo).
        # Extract the RegRef if we can.
        reg_ref = ImplTransformer.match_get_reg(call.func.value)
        if reg_ref is None:
            return updated

        return cst.Assign(targets=[cst.AssignTarget(target=reg_ref)],
                          value=rhs)


def read_implementation(path: str) -> Dict[str, str]:
    '''Read the implementation at path (probably insn.py)

    Returns a dictionary from instruction class name to its pseudo-code
    implementation. An instruction class name looks like ADDI (for addi) or
    BNADDM (for bn.addm).

    '''
    with open(path, 'r') as handle:
        node = cst.parse_module(handle.read())

    # Extract the function bodies
    visitor = ImplTransformer()
    node.visit(visitor)

    # Render the function bodies
    return {cls: ''.join(node.code_for_node(stmt) for stmt in body)
            for cls, body in visitor.impls.items()}
