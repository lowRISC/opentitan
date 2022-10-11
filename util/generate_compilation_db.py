#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""generate_compilation_db.py builds compilation_commands.json from BUILD files.

This tool runs a Bazel Action Graph query (Bazel's "aquery" command) and
transforms the results to produce a compilation database (aka
compile_commands.json). The goal is to enable semantic features like
jump-to-definition and cross-references in IDEs that support
compile_commands.json.

The analysis.ActionGraphContainer protobuf [0] defines aquery's results format.
Clang informally defines the schema of compile_commands.json [1].

Caveat: this tool only emits the commands for building C/C++ code.

Example:
  util/generate_compilation_db.py --target //sw/... --out compile_commands.json

Tip: If your IDE complains that it cannot find headers, e.g. "gmock/gmock.h", it
might be telling the truth. Try building the relevant target with Bazel
(specifying "--config=riscv32" as necessary) and then restart clangd.

[0]: https://github.com/bazelbuild/bazel/blob/master/src/main/protobuf/analysis_v2.proto
[1]: https://clang.llvm.org/docs/JSONCompilationDatabase.html
"""

import argparse
import json
import logging
import os
import subprocess
import sys
from typing import Dict, List, Tuple

logger = logging.getLogger('generate_compilation_db')


def build_id_lookup_dict(dicts: List[Dict]):
    """Create a dict from `dicts` indexed by the "id" key."""
    lookup = {}
    for d in dicts:
        lookup[d['id']] = d
    return lookup


class BazelAqueryResults:
    """Corresponds to Bazel's analysis.ActionGraphContainer protobuf."""

    def __init__(self, output: str):
        parsed = json.loads(output)
        self.actions = [
            BazelAqueryAction(action) for action in parsed['actions']
        ]
        self.dep_sets_ = build_id_lookup_dict(parsed['depSetOfFiles'])
        self.artifacts_ = build_id_lookup_dict(parsed['artifacts'])
        self.path_fragments_ = build_id_lookup_dict(parsed['pathFragments'])

    def reconstruct_path(self, id: int):
        """Reconstruct a file path from Bazel aquery fragments."""
        labels = []

        while True:
            path_fragment = self.path_fragments_[id]
            labels.append(path_fragment['label'])

            if 'parentId' not in path_fragment:
                break
            id = path_fragment['parentId']

        # For our purposes, `os.sep.join()` should be equivalent to
        # `os.path.join()`, but without the additional overhead.
        return os.sep.join(reversed(labels))

    def iter_artifacts_for_dep_sets(self, dep_set_ids: List[int]):
        """Iterate the reconstructed paths of all artifacts related to `dep_set_ids`."""
        SOURCE_EXTENSIONS = [".h", ".c", ".cc"]

        dep_set_id_stack = dep_set_ids
        while len(dep_set_id_stack) > 0:
            dep_set_id = dep_set_id_stack.pop()
            dep_set = self.dep_sets_[dep_set_id]

            for direct_artifact_id in dep_set.get('directArtifactIds', []):
                artifact = self.artifacts_[direct_artifact_id]
                path_fragment_id = artifact['pathFragmentId']
                path = self.reconstruct_path(path_fragment_id)
                if path.startswith("external/"):
                    continue
                if not any(path.endswith(ext) for ext in SOURCE_EXTENSIONS):
                    continue
                yield path

            for transitive_dep_set_id in dep_set.get('transitiveDepSetIds',
                                                     []):
                dep_set_id_stack.append(transitive_dep_set_id)


class BazelAqueryAction:
    """Corresponds to Bazel's analysis.Action protobuf."""

    def __init__(self, action: Dict):
        self.mnemonic = action.get('mnemonic', None)
        self.arguments = action.get('arguments', None)
        self.input_dep_set_ids = action.get('inputDepSetIds', [])

    def transform_arguments_for_clangd(self) -> List[str]:
        """Return modified arguments for compatibility with Clangd.

        It appears that Clangd fails to infer the desired target from the
        compiler name. For instance, this is the path to our cross-compiler:
        `external/crt/toolchains/lowrisc_rv32imcb/wrappers/clang`. Specifically,
        Clangd fails to launch a compiler instance if it sees `--march=rv32imc`
        or `--mabi=ilp32`.

        This function explicitly tells Clangd which target we want by inserting
        a `--target=riscv32` flag as needed.
        """
        args = self.arguments
        if not args:
            return args
        compiler_path = args[0]
        if 'lowrisc_rv32imcb' in compiler_path:
            return [compiler_path, '--target=riscv32'] + args[1:]
        return args


class PathBuilder:
    """Helper class that builds useful paths relative to this source file."""

    def __init__(self, script_path):
        util_dir = os.path.dirname(script_path)
        self.top_dir = os.path.dirname(util_dir)
        if self.top_dir == '':
            raise Exception('Could not find parent of the util directory.')
        self.bazelisk_script = os.path.join(self.top_dir, 'bazelisk.sh')
        # Bazel creates a symlink to execRoot based on the workspace name.
        # https://bazel.build/remote/output-directories
        self.bazel_exec_root = os.path.join(
            self.top_dir, f"bazel-{os.path.basename(self.top_dir)}")


def build_compile_commands(
        paths: PathBuilder,
        device_build: bool) -> Tuple[List[Dict], List[Dict]]:
    bazel_aquery_command = [
        paths.bazelisk_script,
        'aquery',
        '--output=jsonproto',
    ]
    if device_build:
        bazel_aquery_command.append('--config=riscv32')
    bazel_aquery_command.append(f'mnemonic("CppCompile", {args.target})')

    logger.info("Running bazel command: %s", bazel_aquery_command)
    try:
        completed_process = subprocess.run(bazel_aquery_command,
                                           stdout=subprocess.PIPE,
                                           stderr=subprocess.PIPE,
                                           check=True)
    except subprocess.CalledProcessError as e:
        print(e.stderr.decode('utf-8'), file=sys.stderr)
        raise
    except BaseException:
        raise

    logger.info("Processing output from bazel aquery")
    aquery_results = BazelAqueryResults(
        completed_process.stdout.decode('utf-8'))

    compile_commands = []
    unittest_compile_commands = []
    for action in aquery_results.actions:
        assert action.mnemonic == 'CppCompile'
        assert action.arguments != []

        arguments = action.transform_arguments_for_clangd()

        for artifact in aquery_results.iter_artifacts_for_dep_sets(
                action.input_dep_set_ids):
            command = {
                'directory': paths.bazel_exec_root,
                'arguments': arguments,
                'file': artifact,
            }

            if artifact.endswith("_unittest.cc"):
                unittest_compile_commands.append(command)
            else:
                compile_commands.append(command)

    return (compile_commands, unittest_compile_commands)


def main(args):
    paths = PathBuilder(os.path.realpath(__file__))

    device_commands, device_unittest_commands = build_compile_commands(
        paths, device_build=True)
    host_commands, host_unittest_commands = build_compile_commands(
        paths, device_build=False)

    # In case there are conflicting host and device commands for "*_unittest.cc"
    # sources, we strategically place the host commands first. Conversely, we
    # favor the device commands for non-test sources.
    all_compile_commands = device_commands + host_commands + \
        host_unittest_commands + device_unittest_commands

    logger.info("Writing compile commands to %s", args.out)
    compile_commands_json = json.dumps(all_compile_commands, indent=4)
    if not args.out:
        print(compile_commands_json)
        return
    with open(args.out, 'w') as output_file:
        output_file.write(compile_commands_json)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--target',
                        default='//...',
                        help='Bazel target. Default is "//...".')
    parser.add_argument(
        '--out',
        help='Path of output file for compilation DB. Defaults to stdout.')

    if len(sys.argv) == 1:
        parser.print_help()
        sys.exit(1)

    args = parser.parse_args()

    logging.basicConfig(format='%(asctime)s %(message)s')
    logger.setLevel(logging.DEBUG)

    main(args)
