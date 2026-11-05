# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for check-pr-changes-allowed.py."""

import importlib.util
import io
import os
import sys
import tempfile
import types
import unittest
from contextlib import redirect_stdout
from unittest import mock

_SCRIPT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'check-pr-changes-allowed.py')


def _load_script():
    """Import the script, whose file name is not a valid module name.

    The script imports `requests` at module level. A stub is installed while
    importing so the tests need neither the package nor network access. Any
    test that reaches `requests.get` without mocking it fails loudly.
    """
    stub = types.ModuleType('requests')
    stub.get = mock.Mock(side_effect=AssertionError('unexpected network access'))
    with mock.patch.dict(sys.modules, {'requests': stub}):
        spec = importlib.util.spec_from_file_location('check_pr_changes_allowed', _SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    return module


cpca = _load_script()

# Mirrors the layout of the real COMMITTERS file, including the format example
# line and a name with a non-ASCII character.
COMMITTERS_TEXT = """\
Committers are listed alphabetically by surname in the format:
* Full Name (GitHubID)

Committer list:
* Ada Lovelace (ada-l)
* Grace Brewster Hopper (GraceH)
* Luís Marques (luismarques)
"""


class TempDirTestCase(unittest.TestCase):

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmpdir = tmp.name

    def write(self, name: str, text: str) -> str:
        path = os.path.join(self.tmpdir, name)
        with open(path, 'w') as f:
            f.write(text)
        return path


class LoadBlockfileTest(TempDirTestCase):

    def test_ignores_comments_blank_lines_and_whitespace(self):
        path = self.write('BLOCKFILE', '# A comment\n'
                                       '\n'
                                       'hw/ip/aes/rtl/*  # trailing comment\n'
                                       '   BLOCKFILE   \n'
                                       '#hw/commented/out/*\n')
        self.assertEqual(cpca.load_blockfile(path), ['hw/ip/aes/rtl/*', 'BLOCKFILE'])

    def test_empty_file(self):
        path = self.write('BLOCKFILE', '')
        self.assertEqual(cpca.load_blockfile(path), [])


class LoadChangesTest(TempDirTestCase):

    def test_strips_whitespace_and_drops_empty_lines(self):
        path = self.write('changes', 'a/b.sv\n\n  c/d.md  \n\n')
        self.assertEqual(list(cpca.load_changes(path)), ['a/b.sv', 'c/d.md'])


class CheckChangesAgainstBlocklistTest(unittest.TestCase):

    def test_exact_path(self):
        blocked = cpca.check_changes_against_blocklist(['BLOCKFILE', 'README.md'],
                                                       ['BLOCKFILE'])
        self.assertEqual(blocked, {'BLOCKFILE': ['BLOCKFILE']})

    def test_star_matches_across_directory_levels(self):
        # Documented in the BLOCKFILE header: '*' has no special handling of '/'.
        blocked = cpca.check_changes_against_blocklist(
            ['hw/ip/aes/rtl/aes.sv', 'hw/ip/aes/rtl/sub/dir/aes_core.sv'],
            ['hw/ip/aes/rtl/*'])
        self.assertEqual(set(blocked), {'hw/ip/aes/rtl/aes.sv',
                                        'hw/ip/aes/rtl/sub/dir/aes_core.sv'})

    def test_similar_paths_are_not_blocked(self):
        blocked = cpca.check_changes_against_blocklist(
            ['hw/ip/aes/dv/aes_env.sv', 'hw/ip/aes_masked/rtl/x.sv', 'hw/ip/aes/rtl'],
            ['hw/ip/aes/rtl/*'])
        self.assertEqual(blocked, {})

    def test_lists_every_matching_pattern(self):
        blocked = cpca.check_changes_against_blocklist(
            ['hw/top_earlgrey/rtl/top.sv'],
            ['hw/top_earlgrey/rtl/*', 'hw/top_earlgrey/*', 'hw/ip/*'])
        self.assertEqual(blocked, {'hw/top_earlgrey/rtl/top.sv':
                                   ['hw/top_earlgrey/rtl/*', 'hw/top_earlgrey/*']})

    def test_matching_is_case_sensitive(self):
        blocked = cpca.check_changes_against_blocklist(['Blockfile'], ['BLOCKFILE'])
        self.assertEqual(blocked, {})


class LoadCommittersTest(TempDirTestCase):

    def test_parses_names_and_lowercases_handles(self):
        path = self.write('COMMITTERS', COMMITTERS_TEXT)
        self.assertEqual(cpca.load_committers(path), {
            'ada-l': 'Ada Lovelace',
            'graceh': 'Grace Brewster Hopper',
            'luismarques': 'Luís Marques',
        })

    def test_drops_format_example(self):
        path = self.write('COMMITTERS', COMMITTERS_TEXT)
        self.assertNotIn('githubid', cpca.load_committers(path))


class GetAuthorizedChangesTest(unittest.TestCase):

    COMMITTERS = {'ada-l': 'Ada Lovelace', 'graceh': 'Grace Brewster Hopper'}

    def authorized(self, comments):
        return cpca.get_authorized_changes(comments, self.COMMITTERS)

    def test_counts_committers_only(self):
        result = self.authorized([
            ('ada-l', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/aes.sv'),
            ('someone-else', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/aes.sv'),
        ])
        self.assertEqual(result, {'hw/ip/aes/rtl/aes.sv': {'ada-l'}})

    def test_comment_author_is_case_insensitive(self):
        result = self.authorized([('GraceH', 'CHANGE AUTHORIZED: BLOCKFILE')])
        self.assertEqual(result, {'BLOCKFILE': {'graceh'}})

    def test_multiple_files_crlf_and_trailing_spaces(self):
        body = ('LGTM.\r\n'
                'CHANGE AUTHORIZED: hw/a.sv  \r\n'
                'CHANGE AUTHORIZED: hw/b.sv\r\n')
        result = self.authorized([('ada-l', body)])
        self.assertEqual(result, {'hw/a.sv': {'ada-l'}, 'hw/b.sv': {'ada-l'}})

    def test_marker_must_start_the_line(self):
        result = self.authorized([
            ('ada-l', 'Could a committer write CHANGE AUTHORIZED: hw/a.sv ?'),
            ('graceh', '> CHANGE AUTHORIZED: hw/a.sv'),
        ])
        self.assertEqual(result, {})

    def test_repeated_authorization_by_one_committer_counts_once(self):
        result = self.authorized([
            ('ada-l', 'CHANGE AUTHORIZED: hw/a.sv'),
            ('ada-l', 'CHANGE AUTHORIZED: hw/a.sv'),
        ])
        self.assertEqual(result, {'hw/a.sv': {'ada-l'}})


class FetchPrCommentsTest(unittest.TestCase):

    def test_combines_issue_comments_and_review_bodies(self):
        def fake_get(url, headers):
            self.assertEqual(headers['Authorization'], 'Bearer token')
            response = mock.Mock()
            if url.endswith('/issues/42/comments'):
                response.json.return_value = [{'user': {'login': 'ada-l'}, 'body': 'one'}]
            elif url.endswith('/pulls/42/reviews'):
                response.json.return_value = [{'user': {'login': 'graceh'}, 'body': 'two'}]
            else:
                self.fail(f'unexpected URL {url}')
            return response

        with mock.patch.object(cpca.requests, 'get', side_effect=fake_get):
            comments = cpca.fetch_pr_comments('token', 'lowrisc/opentitan', 42)
        self.assertEqual(comments, [('ada-l', 'one'), ('graceh', 'two')])


class MainTest(TempDirTestCase):
    """End-to-end runs of main() with the GitHub API mocked out."""

    def setUp(self):
        super().setUp()
        self.write('BLOCKFILE', 'hw/ip/aes/rtl/*\n')
        self.write('COMMITTERS', COMMITTERS_TEXT)
        # main() reads COMMITTERS from the current directory.
        cwd = os.getcwd()
        os.chdir(self.tmpdir)
        self.addCleanup(os.chdir, cwd)

    def run_main(self, changes, extra_args=(), comments=None):
        changes_file = self.write('changes', '\n'.join(changes) + '\n')
        argv = ['check-pr-changes-allowed', changes_file, '--block-file', 'BLOCKFILE']
        argv += list(extra_args)
        if comments is not None:
            argv += ['--gh-token', 'token', '--pr-number', '42']
        out = io.StringIO()
        with mock.patch.object(sys, 'argv', argv), \
                mock.patch.object(cpca, 'fetch_pr_comments', return_value=comments or []), \
                redirect_stdout(out):
            code = cpca.main()
        return code, out.getvalue()

    def test_no_blocked_changes(self):
        code, out = self.run_main(['hw/ip/aes/doc/README.md'])
        self.assertEqual(code, 0)
        self.assertIn('clear to merge', out)

    def test_blocked_change_without_token(self):
        code, out = self.run_main(['hw/ip/aes/rtl/aes.sv'])
        self.assertEqual(code, 1)
        self.assertIn('hw/ip/aes/rtl/aes.sv blocked by pattern(s): hw/ip/aes/rtl/*', out)

    def test_one_authorization_is_not_enough(self):
        code, _ = self.run_main(['hw/ip/aes/rtl/aes.sv'], comments=[
            ('ada-l', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/aes.sv'),
        ])
        self.assertEqual(code, 1)

    def test_two_committer_authorizations_unblock(self):
        code, out = self.run_main(['hw/ip/aes/rtl/aes.sv'], comments=[
            ('ada-l', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/aes.sv'),
            ('GraceH', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/aes.sv'),
        ])
        self.assertEqual(code, 0)
        self.assertIn('hw/ip/aes/rtl/aes.sv change is authorized by', out)

    def test_authorization_is_per_file(self):
        code, out = self.run_main(['hw/ip/aes/rtl/a.sv', 'hw/ip/aes/rtl/b.sv'], comments=[
            ('ada-l', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/a.sv'),
            ('graceh', 'CHANGE AUTHORIZED: hw/ip/aes/rtl/a.sv'),
        ])
        self.assertEqual(code, 1)
        self.assertIn('hw/ip/aes/rtl/b.sv blocked by', out)
        self.assertNotIn('hw/ip/aes/rtl/a.sv blocked by', out)

    def test_plain_block_msg_prints_only_paths(self):
        code, out = self.run_main(['hw/ip/aes/rtl/aes.sv'], extra_args=['--plain-block-msg'])
        self.assertEqual(code, 1)
        self.assertEqual(out, 'hw/ip/aes/rtl/aes.sv\n')


if __name__ == '__main__':
    unittest.main()
