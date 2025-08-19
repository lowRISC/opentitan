# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
TODO explain
"""
from util.py.packages.lib import bazel
from pathlib import Path
import ast
import subprocess
import os
import json


def run(*args):
    try:
        res = subprocess.run(args,
                             env=os.environ.copy(),
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             encoding='utf8',
                             errors='ignore',
                             check=True)
    except subprocess.CalledProcessError as e:
        print(f"stdout: {e.stdout if e.stdout else '(empty)'}")
        print(f"stderr: {e.stderr if e.stderr else '(empty)'}")
        raise
    return res.stdout


def find_module_assignement(module_ast, target):
    return list(filter(
        lambda stmt: isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and
        isinstance(stmt.targets[0], ast.Name) and stmt.targets[0].id == target,
        module_ast.body,
    ))


def find_python_verison(module_ast):
    python_version = find_module_assignement(module_ast, "PYTHON_VERSION")
    assert len(python_version) > 0, "could not find assignement to PYTHON_VERSION in MODULE.bazel"
    python_version = python_version[0].value
    assert isinstance(python_version, ast.Constant) and isinstance(python_version.value, str), \
        "REPO_RULES_PIP_DIRECT_DEPS is not a string, this script cannot handle that"
    return python_version.value


def find_pip_direct_deps(module_ast):
    pip_direct_deps = find_module_assignement(module_ast, "REPO_RULES_PIP_DIRECT_DEPS")
    assert len(pip_direct_deps) > 0, \
        "could not find assignement to REPO_RULES_PIP_DIRECT_DEPS in MODULE.bazel"
    pip_direct_deps = pip_direct_deps[0].value
    assert isinstance(pip_direct_deps, ast.List), \
        "REPO_RULES_PIP_DIRECT_DEPS is not a list, this script cannot handle that"
    for dep in pip_direct_deps.elts:
        assert isinstance(dep, ast.Constant) and isinstance(dep.value, str), \
            "value in REPO_RULES_PIP_DIRECT_DEPS is not a string, this script cannot handle that"
    return [dep.value for dep in pip_direct_deps.elts]


def find_canonical_name(base_canonical_repo_name, apparent_name):
    # Query repository mapping
    mapping_json = json.loads(run(
        "./bazelisk.sh",
        "mod",
        "dump_repo_mapping",
        base_canonical_repo_name,
    ))
    assert apparent_name in mapping_json, \
        f"repository {base_canonical_repo_name} does not have a mapping to repo {apparent_name}"
    return mapping_json[apparent_name]


def main():
    bazel.try_escape_sandbox()
    module_bazel = Path("MODULE.bazel").read_text()
    # Parse MODULE.bazel
    module_ast = ast.parse(module_bazel)
    # Find python version.
    python_version = find_python_verison(module_ast)
    print("Python version:", python_version)
    # Find the list of direct dependencies.
    pip_direct_deps = find_pip_direct_deps(module_ast)
    print("Direct dependencies listed in MODULE.bazel:", pip_direct_deps)
    # Find canonical name of the ot_python_deps repo: the name of the root repository is empty.
    ot_python_deps_canonical = find_canonical_name("", "ot_python_deps")
    print(f"ot_python_deps cannonical name: {ot_python_deps_canonical}")
    # Now run bazel queries to find all dependencies
    transitive_deps = set(pip_direct_deps)
    todo = set(pip_direct_deps)
    while todo:
        dep = todo.pop()
        # Find the canonical name of this repository
        apparent_repo_name = 'ot_python_deps_{}_{}'.format(python_version.replace(".", ""), dep)
        canonical_repo_name = find_canonical_name(ot_python_deps_canonical, apparent_repo_name)
        print(f"canonical name of {dep} is {canonical_repo_name}")
        rule_desc = run(
            './bazelisk.sh',
            'query',
            '--output=build',
            f'@@{canonical_repo_name}//:pkg',
        )
        rule_desc = ast.parse(rule_desc)
        assert isinstance(rule_desc, ast.Module) and len(rule_desc.body) == 1, \
            "unexpected output format for pkg (not a a single expression)"
        rule_desc = rule_desc.body[0]
        assert isinstance(rule_desc, ast.Expr) and isinstance(rule_desc.value, ast.Call), \
            "unexpected output format for pkg (not a call)"
        assert isinstance(rule_desc.value.func, ast.Name) and \
            rule_desc.value.func.id == "py_library", \
            "unexpected output format for pkg (not a py_library)"
        rules_args = [arg.value for arg in rule_desc.value.keywords if arg.arg == "deps"]
        if rules_args:
            assert isinstance(rules_args[0], ast.List), \
                "unexpected output format for pkg deps (not a list)"
            for rule_dep in rules_args[0].elts if rules_args else []:
                assert isinstance(rule_dep, ast.Constant) and isinstance(rule_dep.value, str), \
                    "unexpected output format for pkg deps (non-constant)"
                this_dep = rule_dep.value
                if not this_dep.startswith('@ot_python_deps//') or not this_dep.endswith(':pkg'):
                    print(f"Warning: ignoring dependency {this_dep} of {dep}")
                    continue
                this_dep = this_dep.removeprefix('@ot_python_deps//').removesuffix(':pkg')
                if this_dep not in transitive_deps and this_dep not in todo:
                    todo.add(this_dep)
                    transitive_deps.add(this_dep)
    # Create assignement
    assign = []
    assign.append("REPO_RULES_PIP_TRANSITIVE_DEPS = [\n")
    for dep in sorted(list(transitive_deps - set(pip_direct_deps))):
        assign.append(f'    "{dep}",\n')
    assign.append("]\n")
    # Edit MODULE.bazel
    transitive_dep_assignement = find_module_assignement(
        module_ast,
        "REPO_RULES_PIP_TRANSITIVE_DEPS"
    )
    assert len(transitive_dep_assignement) == 1, \
        "could not find assignement to REPO_RULES_PIP_TRANSITIVE_DEPS in MODULE.bazel"
    transitive_dep_assignement = transitive_dep_assignement[0]
    module_bazel = module_bazel.splitlines(keepends=True)
    # NOTE: lineno is 1-indexed
    module_bazel[
        transitive_dep_assignement.lineno - 1:transitive_dep_assignement.end_lineno
    ] = assign
    # Write output
    Path("MODULE.bazel").write_text(''.join(module_bazel))


if __name__ == "__main__":
    main()
