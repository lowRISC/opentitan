# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
import tempfile

from util.py.packages.lib.register_usage_report import (
    RegisterTokenPattern, RegisterUsageReport, RegisterUsageReportGroup,
    SingleFileSourceRange)


class TestSingleFileSourceRange(unittest.TestCase):

    def test_hash(self):
        """Test that the hash function incorporates all fields.

        Hash collisions are unlikely, but not impossible, so this test might be flaky.
        """
        self.assertEqual(hash(SingleFileSourceRange("foo", 1, 2)),
                         hash(SingleFileSourceRange("foo", 1, 2)))
        self.assertNotEqual(hash(SingleFileSourceRange("foo", 1, 2)),
                            hash(SingleFileSourceRange("bar", 1, 2)))
        self.assertNotEqual(hash(SingleFileSourceRange("foo", 1, 2)),
                            hash(SingleFileSourceRange("foo", 9, 2)))
        self.assertNotEqual(hash(SingleFileSourceRange("foo", 1, 2)),
                            hash(SingleFileSourceRange("foo", 1, 9)))

    def test_preview(self):

        with tempfile.NamedTemporaryFile() as tf:
            tf.write(b"fn foo() {\n")
            tf.write(b"  let x = 0;\n")
            tf.write(b"  let y = 0;\n")
            tf.write(b"  while x < 10 {\n")
            tf.write(b"    y++;\n")
            tf.write(b"  }\n")
            tf.write(b"}\n")
            tf.flush()

            source_range = SingleFileSourceRange(tf.name, 4, 5)
            preview = source_range.preview()
            preview_lines = preview.split("\n")

            expected_preview_lines = [
                f"{tf.name}:3    let y = 0;",
                f"{tf.name}:4    while x < 10 {{",
                f"{tf.name}:5      y++;",
                f"{tf.name}:6    }}",
                f"{tf.name}:7  }}",
            ]

            self.assertEqual(preview_lines, expected_preview_lines)


class TestRegisterUsageReport(unittest.TestCase):

    def test_merge_trivial(self):
        reports = [
            RegisterUsageReport("foo", dict(), set()),
            RegisterUsageReport("foo", dict(), set()),
        ]
        merged = RegisterUsageReport.merge_reports(reports)
        self.assertEqual(merged.function_name, "foo")
        self.assertEqual(merged.registers_to_callsites, dict())
        self.assertEqual(merged.unparsed_callsites, set())

    def test_merge_single_elements(self):
        registers_to_callsites = {
            "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
        }
        unparsed_callsites = set([SingleFileSourceRange("baz.c", 2, 2)])
        reports = [
            RegisterUsageReport("func_name", registers_to_callsites,
                                unparsed_callsites),
            RegisterUsageReport("func_name", dict(), set()),
        ]
        merged = RegisterUsageReport.merge_reports(reports)
        self.assertEqual(merged.function_name, "func_name")
        self.assertEqual(merged.registers_to_callsites, registers_to_callsites)
        self.assertEqual(merged.unparsed_callsites, unparsed_callsites)

    def test_merge_disjoint(self):
        report1 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_ABC": set([SingleFileSourceRange("foo.c", 1, 4)]),
                "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
            },
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz.c", 3, 4),
            ]))
        report2 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_DEF": set([SingleFileSourceRange("foo2.c", 2, 5)]),
                "REG_TOKEN_UVW": set([SingleFileSourceRange("foo2.c", 43, 46)
                                      ]),
            },
            set([
                SingleFileSourceRange("bar2.c", 2, 3),
                SingleFileSourceRange("baz2.c", 4, 5),
            ]))

        merged = RegisterUsageReport.merge_reports([report1, report2])
        self.assertEqual(merged.function_name, "func_name")
        self.assertEqual(
            merged.registers_to_callsites, {
                "REG_TOKEN_ABC": set([SingleFileSourceRange("foo.c", 1, 4)]),
                "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
                "REG_TOKEN_DEF": set([SingleFileSourceRange("foo2.c", 2, 5)]),
                "REG_TOKEN_UVW": set([SingleFileSourceRange("foo2.c", 43, 46)
                                      ]),
            })
        self.assertEqual(len(merged.registers_to_callsites), 4)
        self.assertEqual(
            merged.unparsed_callsites,
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz.c", 3, 4),
                SingleFileSourceRange("bar2.c", 2, 3),
                SingleFileSourceRange("baz2.c", 4, 5),
            ]))
        self.assertEqual(len(merged.unparsed_callsites), 4)

    def test_merge_overlapping(self):
        report1 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_ABC": set([SingleFileSourceRange("foo.c", 1, 4)]),
                "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
            },
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz.c", 3, 4),
            ]))
        report2 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_ABC": set(
                    [SingleFileSourceRange("baz.c", 100, 101)]),
                "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
            },
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz2.c", 4, 5),
            ]))

        merged = RegisterUsageReport.merge_reports([report1, report2])
        self.assertEqual(merged.function_name, "func_name")
        self.assertEqual(
            merged.registers_to_callsites, {
                "REG_TOKEN_ABC":
                set([
                    SingleFileSourceRange("foo.c", 1, 4),
                    SingleFileSourceRange("baz.c", 100, 101),
                ]),
                "REG_TOKEN_XYZ":
                set([SingleFileSourceRange("bar.c", 42, 45)]),
            })
        self.assertEqual(len(merged.registers_to_callsites), 2)
        self.assertEqual(
            merged.unparsed_callsites,
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz.c", 3, 4),
                SingleFileSourceRange("baz2.c", 4, 5),
            ]))
        self.assertEqual(len(merged.unparsed_callsites), 3)


class TestRegisterUsageReportGroup(unittest.TestCase):

    def test_serialization_roundtrips(self):
        report_groups = [
            RegisterUsageReportGroup({}),
            RegisterUsageReportGroup({
                "foo":
                RegisterUsageReport(
                    "foo",
                    {"func": set([SingleFileSourceRange("foo.c", 1, 2)])},
                    set())
            }),
        ]

        for group in report_groups:
            with self.subTest(group=group):
                group_bytes = group.serialize()
                group_parsed = RegisterUsageReportGroup.deserialize(
                    group_bytes)
                self.assertIsNotNone(group_parsed)
                self.assertEqual(group, group_parsed)

    def test_merge(self):
        self.assertIsNone(RegisterUsageReportGroup.merge([]))
        self.assertEqual(
            RegisterUsageReportGroup.merge([RegisterUsageReportGroup({})]),
            RegisterUsageReportGroup({}))

        report1 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_ABC": set([SingleFileSourceRange("foo.c", 1, 4)]),
                "REG_TOKEN_XYZ": set([SingleFileSourceRange("bar.c", 42, 45)]),
            },
            set([
                SingleFileSourceRange("bar.c", 1, 2),
                SingleFileSourceRange("baz.c", 3, 4),
            ]))
        report2 = RegisterUsageReport(
            "func_name", {
                "REG_TOKEN_DEF": set([SingleFileSourceRange("foo2.c", 2, 5)]),
                "REG_TOKEN_UVW": set([SingleFileSourceRange("foo2.c", 43, 46)
                                      ]),
            },
            set([
                SingleFileSourceRange("bar2.c", 2, 3),
                SingleFileSourceRange("baz2.c", 4, 5),
            ]))
        merged = RegisterUsageReportGroup.merge([
            RegisterUsageReportGroup({"func_name": report1}),
            RegisterUsageReportGroup({"func_name": report2}),
        ])

        self.assertEqual(
            merged,
            RegisterUsageReportGroup({
                "func_name":
                RegisterUsageReport(
                    "func_name", {
                        "REG_TOKEN_ABC":
                        set([SingleFileSourceRange("foo.c", 1, 4)]),
                        "REG_TOKEN_XYZ":
                        set([SingleFileSourceRange("bar.c", 42, 45)]),
                        "REG_TOKEN_DEF":
                        set([SingleFileSourceRange("foo2.c", 2, 5)]),
                        "REG_TOKEN_UVW":
                        set([SingleFileSourceRange("foo2.c", 43, 46)]),
                    },
                    set([
                        SingleFileSourceRange("bar.c", 1, 2),
                        SingleFileSourceRange("baz.c", 3, 4),
                        SingleFileSourceRange("bar2.c", 2, 3),
                        SingleFileSourceRange("baz2.c", 4, 5),
                    ]))
            }))


class TestRegisterTokenPattern(unittest.TestCase):

    def test_empty(self):
        pattern = RegisterTokenPattern([])
        self.assertEqual(pattern.count_wildcards(), 0)
        with self.assertRaises(AssertionError):
            pattern.find_matches([])

    def test_just_wildcard(self):
        pattern = RegisterTokenPattern([None])
        self.assertEqual(pattern.count_wildcards(), 1)
        with self.assertRaises(AssertionError):
            pattern.find_matches([])

    def test_len_mismatch(self):
        pattern = RegisterTokenPattern(["foo"])
        self.assertEqual(pattern.count_wildcards(), 0)
        self.assertIsNone(pattern.find_matches(["foo", "bar"]))

    def test_one_wildcard(self):
        pattern = RegisterTokenPattern(["base_ptr", "+", None])
        self.assertEqual(pattern.count_wildcards(), 1)
        self.assertIsNone(pattern.find_matches(["some", "other", "expr"]))
        self.assertEqual(pattern.find_matches(["base_ptr", "+", "REG_TOKEN"]),
                         ["REG_TOKEN"])

    def test_two_wildcards(self):
        pattern = RegisterTokenPattern(["base_ptr", "*", None, "+", None])
        self.assertEqual(pattern.count_wildcards(), 2)
        self.assertIsNone(pattern.find_matches(["some", "other", "expr"]))
        self.assertEqual(
            pattern.find_matches(
                ["base_ptr", "*", "REG_TOKEN_A", "+", "REG_TOKEN_B"]),
            ["REG_TOKEN_A", "REG_TOKEN_B"])


if __name__ == "__main__":
    unittest.main()
