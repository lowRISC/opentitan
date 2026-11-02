# Coverage Smoke Tests

This directory contains smoke tests for the OpenTitan code coverage collection
system. These tests verify that coverage is correctly reported for various
languages and execution environments.

## Overview

The smoke tests work by executing specific test targets and then validating the
resulting LCOV coverage reports against expected outcomes defined in JSON files.

The verification is performed by the script `util/coverage/run_smoke_test.py`,
which checks for both function coverage and line coverage.

## Running the Tests

To run the coverage smoke tests manually, use the following command:

```bash
python3 util/coverage/run_smoke_test.py \
  sw/device/lib/coverage/smoke/*.coverage.json
```

These tests are also integrated into the CI pipeline through the
`coverage_smoketest` job in `.github/workflows/coverage-quick.yml`, which
executes the smoke test script against all `*.coverage.json` expectation files
in this directory.

## JSON expectation format

The JSON expectation format is as follows:

```json
{
  "tests": [
    "//path/to/my:test_target",
    ...
  ],
  "coverage": {
    "path/to/my/file.c": {
      "funcs": {
        "function_name_1": "hit",
        "function_name_2": "miss",
        "function_name_3": "skip",
        ...
      },
      "lines": {
        "function_name_1() {": "hit",
        " int x = 0;": "miss",
        "// comments": "skip",
        ...
      }
    },
    ...
  }
}
```

The `tests` field contains a list of Bazel targets to be tested. This script
runs coverage for each target individually and confirms that the results match
the expectations specified in the `coverage` field (as opposed to checking the
cumulative coverage of all tests).

Function names in `funcs` correspond to FNDA records in the LCOV report.

Patterns in `lines` are converted to 1-based line numbers by locating the first
occurrence of the string in the source file. These numbers are then checked
against DA records in the report to verify coverage.
