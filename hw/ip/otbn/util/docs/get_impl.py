# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional, Sequence

import libcst as cst
from libcst._nodes.internal import CodegenState, visit_required


def make_aref(name: str, idx: cst.BaseExpression) -> cst.Subscript:
    sub_elt = cst.SubscriptElement(slice=cst.Index(value=idx))
    return cst.Subscript(value=cst.Name(name), slice=[sub_elt])


class NBAssignTarget(cst.AssignTarget):
    '''The target of a (delayed) state update'''
    def _codegen_impl(self, state: CodegenState) -> None:
        with state.record_syntactic_position(self):
            self.target._codegen(state)

        self.whitespace_before_equal._codegen(state)
        # U+21D0 is "Leftwards Double Arrow" (a nice unicode rendering of
        # SystemVerilog's "<=" which doesn't collide with less-than-or-equal.
        state.add_token("\u21d0")
        self.whitespace_after_equal._codegen(state)


class NBAssign(cst.BaseSmallStatement):
    '''An assignment statement that models a (delayed) state update'''

    def __init__(self, target: NBAssignTarget, value: cst.BaseExpression):
        super().__init__()
        self.target = target
        self.value = value

    def _visit_and_replace_children(self,
                                    visitor: cst.CSTVisitorT) -> "NBAssign":
        target = visit_required(self, "target", self.target, visitor)
        value = visit_required(self, "value", self.value, visitor)
        return NBAssign(target=target, value=value)

    def _codegen_impl(self,
                      state: CodegenState,
                      default_semicolon: bool = False) -> None:
        with state.record_syntactic_position(self):
            self.target._codegen(state)
            self.value._codegen(state)

    @staticmethod
    def make(lhs: cst.BaseAssignTargetExpression,
             rhs: cst.BaseExpression) -> 'NBAssign':
        return NBAssign(target=NBAssignTarget(target=lhs),
                        value=rhs)


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

    def leave_Attribute(self,
                        orig: cst.Attribute,
                        updated: cst.Attribute) -> cst.BaseExpression:
        if isinstance(updated.value, cst.Name):
            stem = updated.value.value

            # Strip out "self." references. In the ISS code, a field in the
            # instruction appears as self.field_name. In the documentation, we
            # can treat all the instruction fields as being in scope.
            if stem == 'self':
                return updated.attr

            # Replace state.dmem with DMEM. This is an object in the ISS code,
            # so you see things like state.dmem.load_u32(...). We keep the
            # "object-orientated" style (so DMEM.load_u32(...)) because we need
            # to distinguish between 32-bit and 256-bit loads.
            if stem == 'state' and updated.attr.value == 'dmem':
                return cst.Name(value='DMEM')

        if isinstance(updated.value, cst.Attribute):
            # This attribute looks like A.B.C where B, C are names and A may be
            # a further attribute or it might be a name.
            attr_a = updated.value.value
            attr_b = updated.value.attr.value
            attr_c = updated.attr.value

            if isinstance(attr_a, cst.Name):
                stem = attr_a.value

                # Replace state.csrs.flags with FLAGs: the flag groups are
                # stored in the CSRs in the ISS and the implementation, but
                # logically exist somewhat separately, so we want named
                # reads/writes from them to look different.
                if (stem, attr_b, attr_c) == ('state', 'csrs', 'flags'):
                    return cst.Name(value='FLAGs')

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
    def match_get_reg(call: cst.BaseExpression) -> Optional[cst.Subscript]:
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
            regfile_uname = 'GPRs'
        elif regfile_name == 'wdrs':
            regfile_uname = 'WDRs'
        else:
            return None

        return make_aref(regfile_uname, getreg_idx)

    @staticmethod
    def _spot_reg_read(node: cst.Call) -> Optional[cst.BaseExpression]:
        # Detect
        #
        #    state.gprs.get_reg(FOO).read_unsigned()
        #    state.gprs.get_reg(FOO).read_signed()
        #
        # and replace with the expressions
        #
        #    GPRs[FOO]
        #    from_2s_complement(GPRs[FOO])
        #
        # respectively.

        # In either case, we expect node.func to be some long attribute
        # (representing state.gprs.get_reg(FOO).read_X). For unsigned or
        # signed, we can check that it is indeed an Attribute and that
        # node.args is empty (neither function takes arguments).
        if node.args or not isinstance(node.func, cst.Attribute):
            return None

        # Now, check whether we're calling one of the functions we're
        # interested in.
        if node.func.attr.value == 'read_signed':
            signed = True
        elif node.func.attr.value == 'read_unsigned':
            signed = False
        else:
            return None

        # Check that node.func.value really does represent something of the
        # form "state.gprs.get_reg(FOO)".
        ret = ImplTransformer.match_get_reg(node.func.value)
        if ret is None:
            return None

        if signed:
            # If this is a call to read_signed, we want to wrap the returned
            # value in a call to a fake sign decode function.
            return cst.Call(func=cst.Name('from_2s_complement'),
                            args=[cst.Arg(value=ret)])
        else:
            return ret

    @staticmethod
    def _spot_csr_read(node: cst.Call) -> Optional[cst.BaseExpression]:
        # Detect
        #
        #    state.read_csr(FOO)
        #
        # and replace it with the expression
        #
        #    CSRs[FOO]

        # Check we have exactly one argument
        if len(node.args) != 1:
            return None

        # Check this is state.read_csr
        if not (isinstance(node.func, cst.Attribute) and
                isinstance(node.func.value, cst.Name) and
                node.func.value.value == 'state' and
                node.func.attr.value == 'read_csr'):
            return None

        return make_aref('CSRs', node.args[0].value)

    @staticmethod
    def _spot_wsr_read_idx(node: cst.Call) -> Optional[cst.BaseExpression]:
        # Detect
        #
        #    state.wsrs.read_at_idx(FOO)
        #
        # and replace it with the expression
        #
        #    WSRs[FOO]

        # Check we have exactly one argument
        if len(node.args) != 1:
            return None

        # Check this is state.wsrs.read_at_idx
        if not (isinstance(node.func, cst.Attribute) and
                isinstance(node.func.value, cst.Attribute) and
                isinstance(node.func.value.value, cst.Name) and
                node.func.value.value.value == 'state' and
                node.func.value.attr.value == 'wsrs' and
                node.func.attr.value == 'read_at_idx'):
            return None

        return make_aref('WSRs', node.args[0].value)

    @staticmethod
    def _spot_wsr_read_name(node: cst.Call) -> Optional[cst.BaseExpression]:
        # Detect
        #
        #    state.wsrs.FOO.read_unsigned()
        #
        # and replace it with the expression
        #
        #    FOO

        # Check we have no arguments
        if len(node.args) != 0:
            return None

        # Check this is A.B.C.D for names A, B, C, D.
        if not (isinstance(node.func, cst.Attribute) and
                isinstance(node.func.value, cst.Attribute) and
                isinstance(node.func.value.value, cst.Attribute) and
                isinstance(node.func.value.value.value, cst.Name)):
            return None

        a_name = node.func.value.value.value
        b_name = node.func.value.value.attr
        c_name = node.func.value.attr
        d_name = node.func.attr

        if not (a_name.value == 'state' and
                b_name.value == 'wsrs' and
                d_name.value == 'read_unsigned'):
            return None

        return c_name

    def leave_Call(self,
                   orig: cst.Call,
                   updated: cst.Call) -> cst.BaseExpression:
        # Handle:
        #
        #    state.gprs.get_reg(FOO).read_unsigned()
        #    state.gprs.get_reg(FOO).read_signed()
        #
        reg_read = ImplTransformer._spot_reg_read(updated)
        if reg_read is not None:
            return reg_read

        csr_read = ImplTransformer._spot_csr_read(updated)
        if csr_read is not None:
            return csr_read

        wsr_read_idx = ImplTransformer._spot_wsr_read_idx(updated)
        if wsr_read_idx is not None:
            return wsr_read_idx

        wsr_read_name = ImplTransformer._spot_wsr_read_name(updated)
        if wsr_read_name is not None:
            return wsr_read_name

        return updated

    @staticmethod
    def _spot_reg_write(node: cst.Expr) -> Optional[NBAssign]:
        # Spot
        #
        #   state.gprs.get_reg(foo).write_unsigned(bar)
        #   state.gprs.get_reg(foo).write_signed(bar)
        #
        # and turn them into
        #
        #   GPRs[FOO] = bar
        #   GPRs[FOO] = to_2s_complement(bar)

        if not isinstance(node.value, cst.Call):
            return None

        call = node.value
        if len(call.args) != 1 or not isinstance(call.func, cst.Attribute):
            return None

        value = call.args[0].value

        if call.func.attr.value == 'write_unsigned':
            rhs = value
        elif call.func.attr.value == 'write_signed':
            rhs = cst.Call(func=cst.Name('to_2s_complement'),
                           args=[cst.Arg(value=value)])
        else:
            return None

        # We expect call.func.value to be match state.gprs.get_reg(foo).
        # Extract the array reference if we can.
        reg_ref = ImplTransformer.match_get_reg(call.func.value)
        if reg_ref is None:
            return None

        return NBAssign.make(reg_ref, rhs)

    @staticmethod
    def _spot_csr_write(node: cst.Expr) -> Optional[NBAssign]:
        # Spot
        #
        #   state.write_csr(csr, new_val)
        #
        # and turn it into
        #
        #   CSRs[csr] = new_val

        if not isinstance(node.value, cst.Call):
            return None

        call = node.value
        if len(call.args) != 2 or not isinstance(call.func, cst.Attribute):
            return None

        if not (isinstance(call.func.value, cst.Name) and
                call.func.value.value == 'state' and
                call.func.attr.value == 'write_csr'):
            return None

        idx = call.args[0].value
        rhs = call.args[1].value

        return NBAssign.make(make_aref('CSRs', idx), rhs)

    @staticmethod
    def _spot_wsr_write_idx(node: cst.Expr) -> Optional[NBAssign]:
        # Spot
        #
        #   state.wsrs.write_at_idx(wsr, new_val)
        #
        # and turn it into
        #
        #   WSRs[wsr] = new_val

        if not isinstance(node.value, cst.Call):
            return None

        call = node.value
        if len(call.args) != 2 or not isinstance(call.func, cst.Attribute):
            return None

        func = call.func

        if not (isinstance(func.value, cst.Attribute) and
                isinstance(func.value.value, cst.Name) and
                func.value.value.value == 'state' and
                func.value.attr.value == 'wsrs' and
                func.attr.value == 'write_at_idx'):
            return None

        idx = call.args[0].value
        rhs = call.args[1].value

        return NBAssign.make(make_aref('WSRs', idx), rhs)

    @staticmethod
    def _spot_wsr_write_name(node: cst.Expr) -> Optional[NBAssign]:
        # Spot
        #
        #   state.wsrs.FOO.write_unsigned(new_val)
        #
        # and turn it into
        #
        #   FOO = new_val

        if not isinstance(node.value, cst.Call):
            return None

        call = node.value
        if len(call.args) != 1 or not isinstance(call.func, cst.Attribute):
            return None

        # Check this is A.B.C.D for names A, B, C, D.
        if not (isinstance(call.func, cst.Attribute) and
                isinstance(call.func.value, cst.Attribute) and
                isinstance(call.func.value.value, cst.Attribute) and
                isinstance(call.func.value.value.value, cst.Name)):
            return None

        a_name = call.func.value.value.value
        b_name = call.func.value.value.attr
        c_name = call.func.value.attr
        d_name = call.func.attr

        if not (a_name.value == 'state' and
                b_name.value == 'wsrs' and
                d_name.value == 'write_unsigned'):
            return None

        rhs = call.args[0].value

        return NBAssign.make(c_name, rhs)

    @staticmethod
    def _spot_flag_write(node: cst.Expr) -> Optional[NBAssign]:
        # Spot
        #
        #   state.set_flags(fg, flags)
        #
        # and turn it into
        #
        #   FLAGs[fg] = flags

        if not isinstance(node.value, cst.Call):
            return None

        call = node.value
        if len(call.args) != 2 or not isinstance(call.func, cst.Attribute):
            return None

        if not (isinstance(call.func.value, cst.Name) and
                call.func.value.value == 'state' and
                call.func.attr.value == 'set_flags'):
            return None

        fg = call.args[0].value
        flags = call.args[1].value

        return NBAssign.make(make_aref('FLAGs', fg), flags)

    def leave_Expr(self,
                   orig: cst.Expr,
                   updated: cst.Expr) -> cst.BaseSmallStatement:
        reg_write = ImplTransformer._spot_reg_write(updated)
        if reg_write is not None:
            return reg_write

        csr_write = ImplTransformer._spot_csr_write(updated)
        if csr_write is not None:
            return csr_write

        wsr_write_idx = ImplTransformer._spot_wsr_write_idx(updated)
        if wsr_write_idx is not None:
            return wsr_write_idx

        wsr_write_name = ImplTransformer._spot_wsr_write_name(updated)
        if wsr_write_name is not None:
            return wsr_write_name

        flag_write = ImplTransformer._spot_flag_write(updated)
        if flag_write is not None:
            return flag_write

        return updated

    def leave_Assign(self,
                     orig: cst.Assign,
                     updated: cst.Assign) -> cst.BaseSmallStatement:
        # Handle assignments to state.pc_next and replace them with delayed
        # assignments to PC.

        # We don't handle things like "(foo, state.pc_next) = some_fun()"
        if len(updated.targets) != 1:
            return updated

        tgt = updated.targets[0].target
        if ((isinstance(tgt, cst.Attribute) and
             isinstance(tgt.value, cst.Name) and
             tgt.value.value == 'state' and
             tgt.attr.value == 'pc_next')):
            return NBAssign.make(cst.Name(value='PC'), updated.value)

        return updated


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
