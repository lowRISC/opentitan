# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code for making sense of instruction syntax as defined in insns.yml'''

import re
from typing import Dict, List, Set, Tuple

from .operand import Operand


class SyntaxToken:
    '''An object representing a single token in an instruction's syntax

    See InsnSyntax for more details. The is_literal attribute is true if this
    is a literal hunk of text (rather than an operand name). The text attribute
    either holds the literal syntax or the operand name.

    '''
    def __init__(self, is_literal: bool, text: str) -> None:
        assert text
        self.is_literal = is_literal
        # Make whitespace canonical for literals
        self.text = re.sub(r'\s+', ' ', text) if is_literal else text

    def render_doc(self) -> str:
        '''Return how this syntax token should look in the documentation'''
        if self.is_literal:
            return self.text
        else:
            return '<{}>'.format(self.text)

    def asm_pattern(self) -> str:
        '''Return a regex pattern that can be used for matching this token

        If the token represents an operand, the pattern is wrapped in a group
        (to capture the operand). For more details about the syntax, see
        InsnSyntax.

        '''
        if self.is_literal:
            # A literal that is pure whitespace "requires the whitespace".
            # Otherwise, replace all internal whitespace with \s+ and allow
            # optional whitespace afterwards. To do this easily, we split the
            # literal on whitespace. The result is empty iff it was just
            # whitespace in the first place.
            words = self.text.split()
            if not words:
                return r'\s+'

            # For non-whitespace literals, we disallow leading space and add
            # optional trailing space. This convention should avoid lots of
            # \s*\s* pairs.
            parts = [re.escape(words[0])]
            for w in words[1:]:
                parts.append(r'\s+')
                parts.append(re.escape(w))
            parts.append(r'\s*')

            return ''.join(parts)

        # Otherwise, this is an operand. For now, at least, we're very
        # restrictive for operands. No spaces and no commas (the second rule
        # avoids silliness like "a, b, c" matching a syntax with only two
        # operands by setting the second to "b, c").
        #
        # We also split out ++ and -- separately, to disambiguate things like
        # x1++, which must be parsed as x1 followed by ++.
        #
        # However, we do want to allow things like ".+123". To get this right,
        # suppose S matches any character other than elements of " ,+-". Then
        # we can use a regex like "-?S(\+?-?S)*". This avoids two consecutive +
        # or - signs. It also allows .+-3 (i.e. the current PC minus 3). It
        # doesn't allow .-+3, but we probably don't care.
        #
        # If we want to do better and allow things like
        #
        #    addi x0, x1, 1 + 3
        #
        # then we need to use something more serious than just regexes for
        # parsing.
        s_re = r'[^ ,+\-]'
        not_inc_or_dec = ''.join([r'(?:-?', s_re, r'(?:\+?-?', s_re, r')*)'])
        return ''.join([r'(\+\+|--|', not_inc_or_dec, r')\s*'])

    def render(self,
               cur_pc: int,
               op_vals: Dict[str, int],
               operands: Dict[str, Operand]) -> str:
        '''Generate an assembly listing for this syntax token

        If the syntax token is an operand, that operand is retrieved from
        op_vals and rendered.

        '''
        if self.is_literal:
            return self.text

        assert self.text in op_vals
        assert self.text in operands

        op_type = operands[self.text].op_type
        return op_type.op_val_to_str(op_vals[self.text], cur_pc)


class SyntaxHunk:
    '''An object representing a hunk of syntax that might be optional'''
    def __init__(self,
                 is_optional: bool,
                 tokens: List[SyntaxToken],
                 op_list: List[str],
                 op_set: Set[str]) -> None:
        assert tokens
        self.is_optional = is_optional
        self.tokens = tokens
        self.op_list = op_list
        self.op_set = op_set

    @staticmethod
    def from_list(operands: List[str]) -> 'SyntaxHunk':
        '''Smart constructor for a list of operands with "normal" syntax'''
        assert operands
        comma = SyntaxToken(True, ', ')
        tokens = [SyntaxToken(False, operands[0])]
        for op in operands[1:]:
            tokens.append(comma)
            tokens.append(SyntaxToken(False, op))

        op_set = set(operands)
        assert len(op_set) == len(operands)

        return SyntaxHunk(False, tokens, operands, op_set)

    @staticmethod
    def from_string(mnemonic: str, optional: bool, raw: str) -> 'SyntaxHunk':
        '''Smart constructor that parses YAML syntax (see InsnSyntax)'''
        assert raw

        tokens = []
        op_list = []
        op_set = set()

        parts = re.split(r'<([^>]+)>', raw)
        for idx, part in enumerate(parts):
            # The matches for the regex appear in positions 1, 3, 5, ...
            is_literal = not (idx & 1)
            if ('<' in part or '>' in part) and not is_literal:
                raise ValueError("Syntax for {!r} has hunk {!r} which doesn't "
                                 "seem to surround <operand>s properly."
                                 .format(mnemonic, raw))

            if not is_literal:
                assert part
                if part in op_set:
                    raise ValueError("Syntax for {!r} has hunk {!r} with "
                                     "more than one occurrence of <{}>."
                                     .format(mnemonic, raw, part))
                op_list.append(part)
                op_set.add(part)

            # Only allow empty parts (and skip their tokens) if at one end or
            # the other
            if not part and idx not in [0, len(parts) - 1]:
                raise ValueError("Syntax for {!r} has two adjacent operand "
                                 "tokens, with no intervening syntax."
                                 .format(mnemonic))

            if part:
                tokens.append(SyntaxToken(is_literal, part))

        return SyntaxHunk(optional, tokens, op_list, op_set)

    def render_doc(self) -> str:
        '''Return how this hunk should look in the documentation'''
        parts = []
        for token in self.tokens:
            parts.append(token.render_doc())

        body = ''.join(parts)
        return '[{}]'.format(body) if self.is_optional else body

    def asm_pattern(self) -> str:
        '''Return a regex pattern that can be used for matching this hunk

        The result will have a group per operand. It allows trailing, but not
        leading, space within the hunk.

        '''
        parts = []
        for token in self.tokens:
            parts.append(token.asm_pattern())
        body = ''.join(parts)

        # For an optional hunk, we build it up in the form "(?:foo)?". This
        # puts a non-capturing group around foo and then applies "?"
        # (one-or-more) to it.
        return '(?:{})?'.format(body) if self.is_optional else body

    def render(self,
               cur_pc: int,
               op_vals: Dict[str, int],
               operands: Dict[str, Operand]) -> str:
        '''Return an assembly listing for the hunk given operand values

        If this hunk is optional and all its operands are zero, the hunk is
        omitted (so this function returns the empty string).

        '''
        if self.is_optional:
            required = False
            for op_name in self.op_list:
                if op_vals[op_name] != 0:
                    required = True
                    break

            if not required:
                return ''

        return ''.join(token.render(cur_pc, op_vals, operands)
                       for token in self.tokens)


class InsnSyntax:
    '''A class representing the syntax of an instruction

    An instruction's syntax is specified in the YAML file by writing it out
    with operand names surrounded by angle brackets. For example, a simple NOT
    instruction might have a syntax of

        <dst>, <src>

    which should be interpreted as the following tokens:

        - Operand called 'dst'
        - A literal ','
        - Operand called 'src'

    Between the tokens, whitespace is optional (so "x0 , x1" and "x0,x1" both
    match the syntax above) unless a literal token is just a space, in which
    case some whitespace is required. For example

        <dst> <src>

    would match "x0 x1" but not "x0x1". Whitespace within literal syntax tokens
    means that some space is required, matching the regex \\s+. For example,
    the (rather strange) syntax

       <dst> + - <src>

    would match "x0 + - x1" or "x0+ -x1", but not "x0 +- x1".

    Some operands (and surrounding syntax) might be optional. The optional
    syntax is surrounded by square brackets. Nesting is not supported. For
    example:

       <dst>, <src>[, <offset>]

    would match "x0, x1, 123" or "x0, x1".

    Note that a given syntax might be ambiguous. For example,

       <dst>, <src>[, <offset>][, <flavour>]

    With "x0, x1, 123", is 123 an offset or a flavour? (We choose not to embed
    typing information into the syntax, because that results in very confusing
    assembler error messages). We break ties in the same way as the underlying
    regex engine, assigning the operand to the first group, so 123 is an offset
    in this case. Such syntaxes are rather confusing though, so probably not a
    good idea.

    The parsed syntax is stored as a list of "hunks". Each hunk contains a flag
    showing whether the hunk is optional or required and also a list of
    SyntaxToken objects.

    '''
    def __init__(self,
                 hunks: List[SyntaxHunk],
                 op_list: List[str],
                 op_set: Set[str]) -> None:
        self.hunks = hunks
        self.op_list = op_list
        self.op_set = op_set

    @staticmethod
    def from_list(operands: List[str]) -> 'InsnSyntax':
        '''Smart constructor for a list of operands with "normal" syntax'''
        if not operands:
            return InsnSyntax([], [], set())

        hunk = SyntaxHunk.from_list(operands)
        return InsnSyntax([hunk], hunk.op_list, hunk.op_set)

    @staticmethod
    def from_yaml(mnemonic: str, raw: str) -> 'InsnSyntax':
        '''Parse the syntax in the YAML file'''

        # The raw syntax looks something like
        #
        #    <op0>, <op1>[(<op2>)]
        #
        # to mean that you either have "x0, x1" or "x0, x2(x3)". First, split
        # out the bracketed parts.
        by_left = raw.split('[')
        parts = [(False, by_left[0])]
        for after_left in by_left[1:]:
            split = after_left.split(']', 1)
            if len(split) != 2:
                raise ValueError('Unbalanced or nested [] in instruction '
                                 'syntax for {!r}.'
                                 .format(mnemonic))

            parts += [(True, split[0]), (False, split[1])]

        # Now parts contains a list of pairs (required, txt) where txt is a
        # hunk of the syntax and req is true if this hunk is required. A part
        # might be empty. For example, "[a]b c[d]" with both lead and trail
        # with an empty part. But it shouldn't be empty if it's marked
        # optional: that would be something like "a[]b", which doesn't make
        # much sense.
        hunks = []
        for optional, raw in parts:
            if raw:
                hunks.append(SyntaxHunk.from_string(mnemonic, optional, raw))
            elif optional:
                raise ValueError('Empty [] in instruction syntax for {!r}.'
                                 .format(mnemonic))

        # Collect up operands across the hunks
        op_list = []
        op_set = set()
        for hunk in hunks:
            op_list += hunk.op_list
            op_set |= hunk.op_set

        if len(op_list) != len(op_set):
            raise ValueError('Instruction syntax for {!r} is not '
                             'linear in its operands.'
                             .format(mnemonic))

        return InsnSyntax(hunks, op_list, op_set)

    def render_doc(self) -> str:
        '''Return how this syntax should look in the documentation'''
        return ''.join(hunk.render_doc() for hunk in self.hunks)

    def asm_pattern(self) -> Tuple[str, Dict[str, int]]:
        '''Return a regex pattern and a group name map for this syntax'''
        parts = [r'\s*']
        for hunk in self.hunks:
            parts.append(hunk.asm_pattern())
        parts.append('$')
        pattern = ''.join(parts)

        op_to_grp = {}
        for idx, op in enumerate(self.op_list):
            op_to_grp[op] = 1 + idx

        return (pattern, op_to_grp)

    def render(self,
               cur_pc: int,
               op_vals: Dict[str, int],
               operands: Dict[str, Operand]) -> List[str]:
        '''Return an assembly listing for the given operand fields

        The listings for hunks are returned separately (to allow an instruction
        to support glued_ops). To generate the final listing, concatenate them.

        '''
        return [hunk.render(cur_pc, op_vals, operands) for hunk in self.hunks]
