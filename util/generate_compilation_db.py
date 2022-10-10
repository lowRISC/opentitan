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

[0]: https://github.com/bazelbuild/bazel/blob/master/src/main/protobuf/analysis_v2.proto
[1]: https://clang.llvm.org/docs/JSONCompilationDatabase.html

"""

import argparse
import json
import os
import subprocess
import sys
from typing import Dict, List


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

        return os.path.join(*reversed(labels))

    def iter_artifacts_for_dep_sets(self, dep_set_ids: List[int]):
        """Iterate the reconstructed paths of all artifacts related to `dep_set_ids`."""

        dep_set_id_stack = dep_set_ids
        while len(dep_set_id_stack) > 0:
            dep_set_id = dep_set_id_stack.pop()
            dep_set = self.dep_sets_[dep_set_id]

            for direct_artifact_id in dep_set.get('directArtifactIds', []):
                artifact = self.artifacts_[direct_artifact_id]
                path_fragment_id = artifact['pathFragmentId']
                path = self.reconstruct_path(path_fragment_id)
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


def main(args):
    paths = PathBuilder(os.path.realpath(__file__))

    bazel_aquery_command = [
        paths.bazelisk_script,
        'aquery',
        '--output=jsonproto',
        args.target,
    ]
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
    aquery_results = BazelAqueryResults(completed_process.stdout)

    compile_commands = []
    for action in aquery_results.actions:
        if action.mnemonic != 'CppCompile' or action.arguments == []:
            continue

        for artifact in aquery_results.iter_artifacts_for_dep_sets(
                action.input_dep_set_ids):
            compile_commands.append({
                'directory': paths.bazel_exec_root,
                'arguments': action.arguments,
                'file': artifact,
            })

    compile_commands_json = json.dumps(compile_commands,
                                       sort_keys=True,
                                       indent=4)
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
    args = parser.parse_args()

    main(args)
