# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import sys
from pathlib import Path


def fix_imports() -> str:
    """Enable absolute and relative imports in scripts.

    Absolute and relative imports work when a file is executed as a module, e.g.
    `python3 -m util.foo.bar`, but break when the same file is executed as a script,
    e.g. `python3 util/foo/bar.py`. In OpenTitan, we would like to structure our python
    files freely, use relative imports for ease of maintenance, and be able to run them
    as scripts. This function helps us achieve this goal by updating `sys.path` to
    include the root of the repo and returning the value that the caller should use for
    `__package__`. Modules that use absolute or relative imports should call this
    function if they are imported from a script.

    Typical usage:
        from fix_imports import fix_imports
        __package__ = fix_imports()

    See https://peps.python.org/pep-0328/#relative-imports-and-name.

    Returns
        The value that the caller should use for `__package__`.
    """
    # Get the module that imports this module. `filename` always points to the actual
    # file even when run by bazel.
    frame = sys._getframe(1)
    filename = Path(frame.f_code.co_filename)
    # Find the actual repo root using `filename` instead of `os.getcwd()`. The output of
    # `os.getcwd()` depends whether the script is run by bazel while `filename` is the
    # actual path, i.e. not a path under `execroot`.
    repo_root = None
    # Walk up the tree to avoid additional dependencies.
    for cand_root in [filename] + list(filename.parents):
        # `.git` is a directory in regular repos but a file in worktrees.
        if (cand_root / ".git").exists():
            repo_root = cand_root
            break
    if not repo_root:
        raise RuntimeError("Could not find the root of the repo")
    # Update `sys.path`.
    cwd = Path(os.getcwd())
    # Use a heuristic to determine if run by bazel.
    if "execroot" in cwd.parts and "TEST_TARGET" in os.environ:
        # If run by bazel, add `cwd` to remain in the sandbox.
        new_sys_path = cwd
    else:
        # Otherwise, add the root of the repo to `sys.path` since our `util` folder is
        # at the root of the repo.
        new_sys_path = repo_root
    sys.path.append(str(new_sys_path))
    # The value that `__package__` in the outer frame, i.e. the caller's scope, should
    # be set to so that it can use relative or absolute imports in scripts.
    package = str(filename.parent.relative_to(repo_root)).replace('/', '.')
    return package
