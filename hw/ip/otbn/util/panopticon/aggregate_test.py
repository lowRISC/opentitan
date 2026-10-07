#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for OTBN Panopticon stateful aggregator and cache invalidation."""

import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from hw.ip.otbn.util.panopticon import aggregate


class PanopticonAggregateTest(unittest.TestCase):

    def setUp(self) -> None:
        self.tmp_dir = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp_dir.name)
        self.repo_root = self.root / "repo"
        (self.repo_root / "sw/otbn/crypto").mkdir(parents=True)
        self.asm_file = self.repo_root / "sw/otbn/crypto/foo.s"
        self.asm_file.write_text(
            "  /* comment */\n  bn.add w0, w1, w2\n  bn.sub w3, w4, w5\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.tmp_dir.cleanup()

    def test_fi_accumulation_and_source_invalidation(self) -> None:
        state: dict = {
            "version": 1,
            "fi_targets": {},
            "tvla_targets": {},
            "invalidation_log": [],
        }
        dwarf_map = {
            "0": ["sw/otbn/crypto/foo.s", 2],
            "4": ["sw/otbn/crypto/foo.s", 3],
        }
        payload_1 = {
            "target": "//sw/otbn/crypto/tests/fi:foo_fi_test",
            "elf": "sw/otbn/crypto/foo.elf",
            "elf_sha256": "aaa111",
            "attack_mode": "collision",
            "dwarf_map": dwarf_map,
            "pc_counts": {"0": 4, "4": 2},
            "results": {"0": {"0": False}},
        }
        payload_2 = {
            "target": "//sw/otbn/crypto/tests/fi:foo_fi_test",
            "elf": "sw/otbn/crypto/foo.elf",
            "elf_sha256": "aaa111",
            "attack_mode": "collision",
            "dwarf_map": dwarf_map,
            "pc_counts": {"0": 4, "4": 2},
            "results": {"0": {"1": True}, "4": {"0": False}},
        }

        aggregate.merge_fi_payload(
            state, payload_1, self.repo_root, "2026-10-07T01:00:00Z"
        )
        aggregate.merge_fi_payload(
            state, payload_2, self.repo_root, "2026-10-08T01:00:00Z"
        )

        entry = state["fi_targets"]["//sw/otbn/crypto/tests/fi:foo_fi_test"]
        self.assertEqual(entry["runs_merged"], 2)
        self.assertEqual(entry["results"]["0"], {"0": False, "1": True})
        self.assertEqual(entry["results"]["4"], {"0": False})

        # Project to source lines and check red/green status
        dash = aggregate.build_dashboard_data(state, self.repo_root, "deadbeef")
        lines = dash["files"]["sw/otbn/crypto/foo.s"]["lines"]
        self.assertEqual(lines["2"]["status"], "fail")
        self.assertEqual(lines["2"]["fi_tested"], 2)
        self.assertEqual(lines["2"]["fi_vuln"], 1)
        self.assertEqual(lines["3"]["status"], "pass")

        # Modify foo.s -> next run must invalidate previous data
        self.asm_file.write_text(
            "  /* modified */\n  bn.add w0, w1, w2\n  bn.xor w3, w4, w5\n",
            encoding="utf-8",
        )
        payload_3 = {
            "target": "//sw/otbn/crypto/tests/fi:foo_fi_test",
            "elf": "sw/otbn/crypto/foo.elf",
            "elf_sha256": "bbb222",
            "attack_mode": "collision",
            "dwarf_map": dwarf_map,
            "pc_counts": {"0": 4, "4": 2},
            "results": {"0": {"2": False}},
        }
        aggregate.merge_fi_payload(
            state, payload_3, self.repo_root, "2026-10-09T01:00:00Z"
        )

        reset_entry = state["fi_targets"][
            "//sw/otbn/crypto/tests/fi:foo_fi_test"
        ]
        self.assertEqual(reset_entry["runs_merged"], 1)
        self.assertEqual(reset_entry["results"], {"0": {"2": False}})
        self.assertEqual(len(state["invalidation_log"]), 1)
        self.assertIn("foo.s", state["invalidation_log"][0]["reason"])

    def test_tvla_accumulation_and_t_test(self) -> None:
        state: dict = {
            "version": 1,
            "fi_targets": {},
            "tvla_targets": {},
            "invalidation_log": [],
        }
        dwarf_map = {"0": ["sw/otbn/crypto/foo.s", 2]}

        # Construct a batch with zero difference in model 0 and strong leak in model 1
        zeros = [0] * aggregate.NUM_MODELS
        sums_fixed = list(zeros)
        sums_rand = list(zeros)
        sqs_fixed = list(zeros)
        sqs_rand = list(zeros)

        # 50 fixed traces with value ~10, 50 random traces with value ~2
        sums_fixed[1] = 500
        sqs_fixed[1] = 5050
        sums_rand[1] = 100
        sqs_rand[1] = 250

        payload = {
            "target": "//sw/otbn/crypto/tests/tvla:foo_tvla_test",
            "elf": "sw/otbn/crypto/foo.elf",
            "elf_sha256": "ccc333",
            "t_threshold": 4.5,
            "dwarf_map": dwarf_map,
            "counts": {"0": {"0": [50, 50]}},
            "sums": {"0": {"0": [sums_fixed, sums_rand]}},
            "sum_sqs": {"0": {"0": [sqs_fixed, sqs_rand]}},
        }

        aggregate.merge_tvla_payload(
            state, payload, self.repo_root, "2026-10-07T01:00:00Z"
        )
        aggregate.merge_tvla_payload(
            state, payload, self.repo_root, "2026-10-08T01:00:00Z"
        )

        dash = aggregate.build_dashboard_data(state, self.repo_root, "deadbeef")
        line2 = dash["files"]["sw/otbn/crypto/foo.s"]["lines"]["2"]
        self.assertEqual(line2["tvla_traces"], 200)
        self.assertTrue(line2["tvla_leaking"])
        self.assertEqual(line2["tvla_worst_model"], "Out HD")
        self.assertEqual(line2["status"], "fail")
        self.assertIn("1 leak(s)", dash["targets"][0]["findings"])

    def test_deleted_source_and_zip_deduplication(self) -> None:
        state: dict = {
            "version": 1,
            "fi_targets": {},
            "tvla_targets": {},
            "invalidation_log": [],
        }
        payload = {
            "target": "//sw/otbn/crypto/tests/fi:foo_fi_test",
            "elf": "sw/otbn/crypto/foo.elf",
            "elf_sha256": "aaa111",
            "attack_mode": "collision",
            "dwarf_map": {"0": ["sw/otbn/crypto/foo.s", 2]},
            "pc_counts": {"0": 4},
            "results": {"0": {"0": False}},
        }

        # Write both loose fi_results.json and outputs.zip in the same dir
        artifacts_dir = self.root / "artifacts"
        artifacts_dir.mkdir()
        (artifacts_dir / "fi_results.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        with zipfile.ZipFile(artifacts_dir / "outputs.zip", "w") as zf:
            zf.writestr("fi_results.json", json.dumps(payload))

        fi_payloads, _ = aggregate.discover_artifacts(artifacts_dir)
        self.assertEqual(len(fi_payloads), 1)

        aggregate.merge_fi_payload(
            state, fi_payloads[0], self.repo_root, "2026-10-08T01:00:00Z"
        )
        self.assertIn(
            "//sw/otbn/crypto/tests/fi:foo_fi_test", state["fi_targets"]
        )

        # Delete foo.s -> invalidate_stale_repo_targets must purge the target
        self.asm_file.unlink()
        aggregate.invalidate_stale_repo_targets(
            state, self.repo_root, "2026-10-09T01:00:00Z"
        )
        self.assertEqual(state["fi_targets"], {})
        self.assertEqual(len(state["invalidation_log"]), 1)
        self.assertIn("foo.s", state["invalidation_log"][0]["reason"])


if __name__ == "__main__":
    unittest.main()
