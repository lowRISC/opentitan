# lowRISC's Miscellaneous Linters

## About the project

These are linters and checkers, usually for source code, which we have written
for various lowRISC projects.

They include
* `licence-checker/licence-checker.py` which will ensure source code in your
  repository contains correctly formatted licence headers. This is designed to
  be reused: it is configured with `licence-checker.hjson`.

## Using the linters

This repository provides Bazel rules for generating linting jobs. First, add
this repository to your `WORKSPACE` (with a name like `lowrisc_lint`). Then,
in `WORKSPACE` add

```bazel
load("@lowrisc_lint//rules:deps.bzl", "lowrisc_misc_linters_dependencies")
lowrisc_misc_linters_dependencies()
load("@lowrisc_lint//rules:pip.bzl", "lowrisc_misc_linters_pip_dependencies")
lowrisc_misc_linters_pip_dependencies()
```

and then in a BUILD file, like the root:

```bazel
load("@lowrisc_lint//rules:rules.bzl", "licence_check")

licence_check(
    name = "licence-check",
    licence = '''
    Copyright lowRISC contributors.
    Licensed under the Apache License, Version 2.0, see LICENSE for details.
    SPDX-License-Identifier: Apache-2.0
    ''',
    exclude_patterns = [".style.yapf"],
)
```

This will generate a rule that will check licence headers, callable as
`bazel run //:licence-check`.

## How to contribute

Have a look at [CONTRIBUTING](./CONTRIBUTING.md) for guidelines on how to
contribute code to this repository.

## Licensing

Unless otherwise noted, everything in this repository is covered by the Apache
License, Version 2.0 (see [LICENSE](./LICENSE) for full text).
