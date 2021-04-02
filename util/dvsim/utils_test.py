# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''pytest-based testing for functions in utils.py'''

import os
import pytest
from .utils import _subst_wildcards, subst_wildcards


def test_subst_wildcards():
    '''Pytest-compatible test for the subst_wildcards function.'''
    # Basic checks
    assert subst_wildcards('foo {x} baz', {'x': 'bar'}) == 'foo bar baz'

    # Stringify
    assert (subst_wildcards('{a}, {b}, {c}, {d}',
                            {'a': 'a', 'b': True, 'c': 42, 'd': ['{b}', 10]}) ==
            'a, 1, 42, 1 10')

    # Ignored wildcards (with or without a match in mdict)
    assert (subst_wildcards('{a} {b}', {'a': 'aye', 'b': 'bee'},
                            ignored_wildcards=['a']) ==
            '{a} bee')
    assert (subst_wildcards('{a} {b}', {'b': 'bee'},
                            ignored_wildcards=['a']) ==
            '{a} bee')

    # Environment variables. We will always have PWD and can probably assume
    # that this won't itself have any braced substrings.
    assert (subst_wildcards('{PWD}', {}) == os.environ['PWD'])

    # Missing variable with ignore_error=False, running _subst_wildcards
    # instead so that we can catch the error. (We assume that 'biggles' isn't
    # in the environment)
    with pytest.raises(ValueError) as excinfo:
        _subst_wildcards('{biggles} {b}', {'b': 'bee'}, [], False, [])
    assert "unknown wildcard, '{biggles}'" in str(excinfo.value)

    # ignore_error=True.
    assert (subst_wildcards('{biggles} {b}', {'b': 'bee'},
                            ignore_error=True) ==
            '{biggles} bee')

    # Check we support (non-circular) recursion
    assert (subst_wildcards('{a}', {'a': '{b}', 'b': 'c'}) == 'c')

    # Check we spot circular recursion
    with pytest.raises(ValueError) as excinfo:
        _subst_wildcards('{a}', {'a': '{b}', 'b': '{a}'}, [], False, [])
    assert "circular expansion of wildcard '{a}'" in str(excinfo.value)

    # Check we also complain about circular recursion with ignore_error
    with pytest.raises(ValueError) as excinfo:
        _subst_wildcards('{a}', {'a': '{b}', 'b': '{a}'}, [], True, [])
    assert "circular expansion of wildcard '{a}'" in str(excinfo.value)

    # Computed variable names (probably not a great idea, but it's probably
    # good to check this works the way we think)
    assert subst_wildcards('{a}b}', {'a': 'a {', 'b': 'bee'}) == 'a bee'

    # Some eval_cmd calls (using echo, which should always work)
    assert (subst_wildcards('{eval_cmd}echo foo {b}', {'b': 'bar'}) ==
            'foo bar')

    assert (subst_wildcards('foo {eval_cmd}echo {b}', {'b': 'bar'}) ==
            'foo bar')

    # Make sure that nested commands work
    assert (subst_wildcards('{eval_cmd} {eval_cmd} echo echo a', {}) == 'a')

    # Recursive expansion
    assert (subst_wildcards('{var}',
                            {
                                'var': '{{foo}_xyz_{bar}}',
                                'foo': 'p',
                                'bar': 'q',
                                'p_xyz_q': 'baz'
                            }) == 'baz')
