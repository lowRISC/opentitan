# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest

from generate_compilation_db import (BazelAqueryAction, BazelAqueryResults,
                                     PathBuilder)


class TestGenerateCompilationDb(unittest.TestCase):

    def test_bazel_aquery_results(self):
        results = BazelAqueryResults(BAZEL_AQUERY_RESULTS_SMALL)

        # There should be a single "CppCompile" action.
        matching_actions = [
            a for a in results.actions if a.mnemonic == 'CppCompile'
        ]
        self.assertEqual(len(matching_actions), 1)
        action = matching_actions[0]

        self.assertEqual(action.arguments, [
            '/usr/bin/gcc', '-Wall', '-iquote', '.', '-isystem',
            'external/googletest/googlemock', '-fno-canonical-system-headers',
            '-c', 'sw/device/lib/crypto/otbn_util.c', '-o',
            'bazel-out/k8-fastbuild/bin/sw/device/' +
            'lib/crypto/_objs/otbn_util/otbn_util.pic.o'
        ])
        self.assertEqual(action.input_dep_set_ids, [2])

        self.assertEqual(results.reconstruct_path(6),
                         'sw/device/lib/crypto/otbn_util.h')

        self.assertEqual(list(results.iter_artifacts_for_dep_sets([2])), [
            'sw/device/lib/crypto/otbn_util.c',
        ])


class TestBazelAqueryAction(unittest.TestCase):

    def test_transform_arguments_for_clangd(self):
        # Empty arguments is a no-op.
        action = BazelAqueryAction({'arguments': []})
        self.assertEqual(action.transform_arguments_for_clangd(), [])

        # No-op when compiler doesn't look like it targets RISC-V.
        action = BazelAqueryAction({'arguments': ['foo']})
        self.assertEqual(action.transform_arguments_for_clangd(), ['foo'])

        # Same, but with more flags.
        action = BazelAqueryAction({
            'arguments':
            ['foo', '-march=rv32imc', 'bar', '-mabi=ilp32', 'baz']
        })
        self.assertEqual(
            action.transform_arguments_for_clangd(),
            ['foo', '-march=rv32imc', 'bar', '-mabi=ilp32', 'baz'])

        # Insert `--target` flag when the compiler looks like it targets RISC-V.
        action = BazelAqueryAction({
            'arguments': [
                'path/lowrisc_rv32imcb/compiler', '-march=rv32imc',
                '-mabi=ilp32'
            ]
        })
        self.assertEqual(action.transform_arguments_for_clangd(), [
            'path/lowrisc_rv32imcb/compiler', '--target=riscv32',
            '-march=rv32imc', '-mabi=ilp32'
        ])


class TestPathBuilder(unittest.TestCase):

    def test_normal_checkout(self):
        paths = PathBuilder("/foo/bar/opentitan-repo/util/source.py")
        self.assertEqual(paths.top_dir, "/foo/bar/opentitan-repo")
        self.assertEqual(paths.bazelisk_script,
                         "/foo/bar/opentitan-repo/bazelisk.sh")
        self.assertEqual(paths.bazel_exec_root,
                         "/foo/bar/opentitan-repo/bazel-opentitan-repo")

    def test_worktree(self):
        paths = PathBuilder(
            "/foo/bar/opentitan-repo/some-worktree/util/source.py")
        self.assertEqual(paths.top_dir,
                         "/foo/bar/opentitan-repo/some-worktree")
        self.assertEqual(paths.bazelisk_script,
                         "/foo/bar/opentitan-repo/some-worktree/bazelisk.sh")
        self.assertEqual(
            paths.bazel_exec_root,
            "/foo/bar/opentitan-repo/some-worktree/bazel-some-worktree")

    def test_relative_path(self):
        paths = PathBuilder(
            "foo/bar/opentitan-repo/some-worktree/util/source.py")
        self.assertEqual(paths.top_dir, "foo/bar/opentitan-repo/some-worktree")
        self.assertEqual(paths.bazelisk_script,
                         "foo/bar/opentitan-repo/some-worktree/bazelisk.sh")
        self.assertEqual(
            paths.bazel_exec_root,
            "foo/bar/opentitan-repo/some-worktree/bazel-some-worktree")

    def test_relative_path_short(self):
        paths = PathBuilder("foo/util/source.py")
        self.assertEqual(paths.top_dir, "foo")
        self.assertEqual(paths.bazelisk_script, "foo/bazelisk.sh")
        self.assertEqual(paths.bazel_exec_root, "foo/bazel-foo")

    def test_relative_path_too_short(self):
        with self.assertRaises(Exception):
            PathBuilder("util/source.py")


# A pared-down example of Bazel aquery output. Generated with `./bazelisk.sh
# aquery --output=jsonproto '//sw/device/lib/crypto:otbn_util'`.
BAZEL_AQUERY_RESULTS_SMALL = r"""
{
  "artifacts": [{
    "id": 1,
    "pathFragmentId": 1
  }, {
    "id": 2,
    "pathFragmentId": 6
  }, {
    "id": 3,
    "pathFragmentId": 11
  }, {
    "id": 4,
    "pathFragmentId": 12
  }, {
    "id": 5,
    "pathFragmentId": 15
  }, {
    "id": 6,
    "pathFragmentId": 16
  }],
  "actions": [{
    "targetId": 1,
    "actionKey": "709e80c88487a2411e1ee4dfb9f22a861492d20c4765150c0c794abd70f8147c",
    "mnemonic": "Middleman",
    "configurationId": 1,
    "inputDepSetIds": [1],
    "outputIds": [3],
    "primaryOutputId": 3,
    "executionPlatform": "@local_config_platform//:host"
  }, {
    "targetId": 1,
    "actionKey": "e0abcf3f57dcd54d61576eb49b6a4911ed9fc6af72d3dd61548d6e396e8736c4",
    "mnemonic": "CppCompile",
    "configurationId": 1,
    "arguments": ["/usr/bin/gcc", "-Wall", "-iquote", ".", "-isystem",
        "external/googletest/googlemock", "-fno-canonical-system-headers", "-c",
        "sw/device/lib/crypto/otbn_util.c", "-o",
        "bazel-out/k8-fastbuild/bin/sw/device/lib/crypto/_objs/otbn_util/otbn_util.pic.o"],
    "inputDepSetIds": [2],
    "outputIds": [7, 8],
    "discoversInputs": true,
    "primaryOutputId": 7,
    "executionPlatform": "@local_config_platform//:host"
  }],
  "targets": [{
    "id": 1,
    "label": "//sw/device/lib/crypto:otbn_util",
    "ruleClassId": 1
  }],
  "depSetOfFiles": [{
    "id": 1,
    "directArtifactIds": [1, 2]
  }, {
    "id": 3,
    "directArtifactIds": [4, 5, 6]
  }, {
    "id": 2,
    "transitiveDepSetIds": [3],
    "directArtifactIds": [3]
  }],
  "configuration": [{
    "id": 1,
    "mnemonic": "k8-fastbuild",
    "platformName": "k8",
    "checksum": "b617ac78fd0cd265dcf958077ac7aae01530f6896f0958308502ccf9026482e6"
  }],
  "ruleClasses": [{
    "id": 1,
    "name": "cc_library"
  }],
  "pathFragments": [{
    "id": 5,
    "label": "bazel-out"
  }, {
    "id": 4,
    "label": "k8-fastbuild",
    "parentId": 5
  }, {
    "id": 3,
    "label": "internal",
    "parentId": 4
  }, {
    "id": 2,
    "label": "_middlemen",
    "parentId": 3
  }, {
    "id": 1,
    "label": "_S_Ssw_Sdevice_Slib_Scrypto_Sdrivers_Cotbn-BazelCppSemantics_build_arch_k8-fastbuild",
    "parentId": 2
  }, {
    "id": 10,
    "label": "sw"
  }, {
    "id": 9,
    "label": "device",
    "parentId": 10
  }, {
    "id": 8,
    "label": "lib",
    "parentId": 9
  }, {
    "id": 7,
    "label": "crypto",
    "parentId": 8
  }, {
    "id": 6,
    "label": "otbn_util.h",
    "parentId": 7
  }, {
    "id": 11,
    "label": "_S_Ssw_Sdevice_Slib_Scrypto_Cotbn_Uutil-BazelCppSemantics_build_arch_k8-fastbuild",
    "parentId": 2
  }, {
    "id": 14,
    "label": "external"
  }, {
    "id": 13,
    "label": "local_config_cc",
    "parentId": 14
  }, {
    "id": 12,
    "label": "builtin_include_directory_paths",
    "parentId": 13
  }, {
    "id": 15,
    "label": "otbn_util.c",
    "parentId": 7
  }, {
    "id": 19,
    "label": "bazel_tools",
    "parentId": 14
  }, {
    "id": 18,
    "label": "tools",
    "parentId": 19
  }, {
    "id": 17,
    "label": "cpp",
    "parentId": 18
  }, {
    "id": 16,
    "label": "grep-includes.sh",
    "parentId": 17
  }, {
    "id": 27,
    "label": "bin",
    "parentId": 4
  }, {
    "id": 26,
    "label": "sw",
    "parentId": 27
  }, {
    "id": 25,
    "label": "device",
    "parentId": 26
  }, {
    "id": 24,
    "label": "lib",
    "parentId": 25
  }, {
    "id": 23,
    "label": "crypto",
    "parentId": 24
  }, {
    "id": 22,
    "label": "_objs",
    "parentId": 23
  }, {
    "id": 21,
    "label": "otbn_util",
    "parentId": 22
  }, {
    "id": 20,
    "label": "otbn_util.pic.o",
    "parentId": 21
  }, {
    "id": 28,
    "label": "otbn_util.pic.d",
    "parentId": 21
  }, {
    "id": 29,
    "label": "libotbn_util.a-2.params",
    "parentId": 23
  }, {
    "id": 30,
    "label": "libotbn_util.a",
    "parentId": 23
  }, {
    "id": 31,
    "label": "libotbn_util.so-2.params",
    "parentId": 23
  }, {
    "id": 32,
    "label": "build_interface_so",
    "parentId": 17
  }, {
    "id": 33,
    "label": "link_dynamic_library.sh",
    "parentId": 17
  }, {
    "id": 34,
    "label": "libotbn_util.so",
    "parentId": 23
  }, {
    "id": 36,
    "label": "_solib_k8",
    "parentId": 27
  }, {
    "id": 35,
    "label": "libsw_Sdevice_Slib_Scrypto_Slibotbn_Uutil.so",
    "parentId": 36
  }]
}
"""

if __name__ == '__main__':
    unittest.main()
