# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
from pathlib import Path

from util.py.packages.lib.run import run


BAZEL_CMD = "./bazelisk.sh"


def try_escape_sandbox():
    """Escape the Bazel sandbox if necessary.

    Without this step, other functions in this package will be unable to find
    "bazelisk.sh" when invoked via Bazel.
    """
    workspace_dir = os.environ.get('BUILD_WORKSPACE_DIRECTORY')
    if workspace_dir:
        os.chdir(workspace_dir)


def build_target(target: str, configs: list[str]) -> None:
    config_flags = [f"--config={c}" for c in configs]
    run(BAZEL_CMD, "build", *config_flags, target)


def get_rule_deps_of_kind(target: str, kind: str) -> list[str]:
    return run(
        BAZEL_CMD, "query",
        f"kind('^{kind} rule$', deps('{target}') ^ siblings('{target}'))")


def get_target_files_with_ext(target: str, configs: list[str],
                              ext: str) -> list[Path]:
    config_flags = [f"--config={c}" for c in configs]
    starlark_list = f"[f.path for f in target.files.to_list() if f.path.endswith('.{ext}')]"
    paths = run(BAZEL_CMD, "cquery", *config_flags, "--output=starlark",
                f"--starlark:expr='\\n'.join({starlark_list})", target)
    return [Path(p) for p in paths]
