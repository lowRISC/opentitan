# -*- coding: utf-8 -*-
"""
     Hjson Lexer for pygments
     ~~~~~~~~~~~~~~~~~~~~~~~~

     Derived from JsonLexer in pygments.lexers.data
     which is
     :copyright: Copyright 2006-2017 by the Pygments team, see AUTHORS.
     :license: BSD, see pygments LICENSE for details.

     Modifications copyright lowRisc contributors
"""

import re

from pygments.lexer import RegexLexer, include
from pygments.token import (Comment, Error, Keyword, Literal, Name, Number,
                            Punctuation, String, Text)


class HjsonLexer(RegexLexer):
    """
     For HJSON data structures.

     .. versionadded:: 1.5
     """

    name = 'HJSON'
    aliases = ['hjson']
    filenames = ['*.hjson']
    mimetypes = ['application/hjson']

    flags = re.DOTALL

    # integer part of a number
    int_part = r'-?(0|[1-9]\d*)'

    # fractional part of a number
    frac_part = r'\.\d+'

    # exponential part of a number
    exp_part = r'[eE](\+|-)?\d+'

    tokens = {
        'whitespace': [
            (r'\s+', Text),
        ],

        # represents a simple terminal value
        'simplevalue': [
            (r'(true|false|null)\b', Keyword.Constant),
            (('%(int_part)s(%(frac_part)s%(exp_part)s|'
              '%(exp_part)s|%(frac_part)s)') % vars(), Number.Float),
            (int_part, Number.Integer),
            (r'"(\\\\|\\"|[^"])*"', String.Double),
        ],

        # the right hand side of an object, after the attribute name
        'objectattribute': [
            include('value'),
            (r':', Punctuation),
            # triple quote is a multiline string
            # accept any non-quote, single quote plus non-quote
            # two quotes plus non-quote to cover all cases
            (r"'''([^']|'[^']|''[^'])*'''", Text),
            # comma terminates the attribute but expects more
            (r',', Punctuation, '#pop'),
            # a closing bracket terminates the entire object, so pop twice
            (r'\}', Punctuation, '#pop:2'),
            # comma is optional in hjson so terminate on anything else
            # but use re syntax so this match does not consume it
            # This is should really only be done if a value or string matched
            (r'(?=.)', Text, '#pop'),
        ],

        # a json object - { attr, attr, ... }
        'objectvalue': [
            include('whitespace'),
            # a comment
            (r'#[^\n]*', Comment.Single),
            (r'//[^\n]*', Comment.Single),
            (r'"(\\\\|\\"|[^"])*"|(\\\\|[^:])*', Name.Tag, 'objectattribute'),
            (r'\}', Punctuation, '#pop'),
        ],

        # json array - [ value, value, ... }
        'arrayvalue': [
            include('whitespace'),
            (r'#[^\n]*', Comment.Single),
            (r'//[^\n]*', Comment.Single),
            include('value'),
            (r',', Punctuation),
            (r'\]', Punctuation, '#pop'),
        ],

        # a json value - either a simple value or a complex value
        # (object or array)
        'value': [
            include('whitespace'),
            (r'#[^\n]*', Comment.Single),
            (r'//[^\n]*', Comment.Single),
            include('simplevalue'),
            (r'\{', Punctuation, 'objectvalue'),
            (r'\[', Punctuation, 'arrayvalue'),
        ],

        # the root of a json document whould be a value
        'root': [
            (r'#[^\n]*', Comment.Single),
            (r'//[^\n]*', Comment.Single),
            include('value'),
            # hjson does not require the outer {}
            # this is also helpful for styleguide examples!
            include('objectvalue'),
        ],
    }
