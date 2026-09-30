# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import subprocess
import sys
from pathlib import Path

import hjson
import pytest

from LintParser import LintParser


@pytest.mark.parametrize('diagnostic', ['', '%Warning-WIDTH: width mismatch',
                                        '%Error-PINNOTFOUND: missing pin'])
def test_fusesoc_failure_status(tmp_path, diagnostic):
    failure = "ERROR: Failed to build test:core:0.1 : 'make' exited with an error code"
    logfile = tmp_path / 'lint.log'
    logfile.write_text(diagnostic + '\n' + failure + '\n')
    outfile = tmp_path / 'results.hjson'
    script = Path(__file__).with_name('verilator-report-parser.py')
    result = subprocess.run([sys.executable, str(script), '--repfile',
                             str(logfile), '--outfile', str(outfile)],
                            capture_output=True, text=True)
    assert result.returncode == 1, result.stdout + result.stderr
    report = hjson.loads(outfile.read_text())
    assert report['flow_error'] == ([] if diagnostic else [failure])


@pytest.mark.parametrize('failures', [[], ['build failed'], ['one', 'two']])
def test_fallback_message_count(failures):
    parser = LintParser()
    parser.buckets['fusesoc-error'] = failures
    counts = parser.get_results({})
    assert counts == {'info': 0, 'warning': 0, 'error': len(failures)}
    assert parser.buckets['flow_error'] == failures
    assert 'fusesoc-error' not in parser.buckets
