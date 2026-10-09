#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Stateful aggregator and source-level report bundler for OTBN Panopticon.

Maintains cumulative Fault Injection (FI) and TVLA side-channel accumulators
across nightly CI runs, automatically invalidating per-target state whenever
the underlying OTBN ELF or assembly (.s) source files change, and projects
per-PC results onto assembly source lines via DWARF debug info.
"""

import argparse
import base64
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple
import zipfile

from hw.ip.otbn.util.otbn_fi_campaign import MAX_PC_DEPTH
from hw.ip.otbn.util.otbn_tvla_campaign import (
    MODEL_NAMES,
    NUM_MODELS,
    TVLAAccumulator,
)

MAX_INVALIDATION_LOG = 20


def compute_file_sha256(path: Path) -> Optional[str]:
    """Returns the SHA-256 hex digest of a file, or None if missing."""
    if not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_source_path(filepath: str) -> str:
    """Maps generated TVLA *_short.s paths to canonical sw/otbn/crypto/*.s."""
    marker = "/bin/sw/otbn/crypto/tests/tvla/"
    if filepath.startswith("bazel-out/") and marker in filepath:
        fname = filepath.split(marker, 1)[1]
        if fname.endswith("_short.s"):
            return "sw/otbn/crypto/" + fname[:-len("_short.s")] + ".s"
    return filepath


def compute_source_hashes(
    repo_root: Path, dwarf_map: Dict[str, Any]
) -> Dict[str, str]:
    """Computes SHA-256 hashes for all existing source files in dwarf_map."""
    files = {
        normalize_source_path(str(loc[0]))
        for loc in dwarf_map.values()
        if isinstance(loc, (list, tuple)) and len(loc) >= 2
    }
    hashes: Dict[str, str] = {}
    for rel_path in sorted(files):
        digest = compute_file_sha256(repo_root / rel_path)
        if digest is not None:
            hashes[rel_path] = digest
    return hashes


def check_invalidation_reason(
    existing: Dict[str, Any],
    new_elf_sha256: Optional[str],
    current_src_hashes: Dict[str, str],
) -> Optional[str]:
    """Returns a human-readable invalidation reason if stale, or None."""
    old_src_hashes = existing.get("source_hashes", {})
    changed_files = [
        os.path.basename(src_path)
        for src_path, old_hash in old_src_hashes.items()
        if current_src_hashes.get(src_path) != old_hash
    ]
    if changed_files:
        return "Source changed: " + ", ".join(sorted(changed_files))

    if (
        new_elf_sha256 is not None and
        existing.get("elf_sha256") != new_elf_sha256
    ):
        return "ELF binary changed"

    return None


def _open_json(path: Path, mode: str) -> Any:
    if path.name.endswith(".gz"):
        return gzip.open(path, mode + "t", encoding="utf-8")
    return open(path, mode, encoding="utf-8")


def load_state(state_path: Optional[Path]) -> Dict[str, Any]:
    """Loads cumulative Panopticon state from JSON or gzipped JSON."""
    empty_state: Dict[str, Any] = {
        "version": 1,
        "updated_at": "",
        "commit": "",
        "fi_targets": {},
        "tvla_targets": {},
        "invalidation_log": [],
    }
    if state_path is None or not state_path.is_file():
        return empty_state

    try:
        with _open_json(state_path, "r") as f:
            data = json.load(f)
        if isinstance(data, dict) and data.get("version") == 1:
            return data
    except Exception as exc:
        print(f"Warning: Failed to load state from {state_path}: {exc}")

    return empty_state


def save_state(state: Dict[str, Any], state_path: Path) -> None:
    """Writes cumulative Panopticon state to JSON or gzipped JSON."""
    state_path.parent.mkdir(parents=True, exist_ok=True)
    indent = None if state_path.name.endswith(".gz") else 2
    with _open_json(state_path, "w") as f:
        json.dump(state, f, indent=indent)


def discover_artifacts(
    input_dir: Path,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Finds and parses fi_results.json and tvla_accumulators.json files."""
    fi_payloads: List[Dict[str, Any]] = []
    tvla_payloads: List[Dict[str, Any]] = []

    if not input_dir.exists():
        return fi_payloads, tvla_payloads

    artifact_buckets = {
        "fi_results.json": fi_payloads,
        "tvla_accumulators.json": tvla_payloads,
    }

    def _add_if_valid(bucket: List[Dict[str, Any]], obj: Any) -> None:
        if isinstance(obj, dict) and "dwarf_map" in obj:
            bucket.append(obj)

    for root, dirs, files in os.walk(input_dir, followlinks=True):
        dirs.sort()
        file_set = set(files)
        root_path = Path(root)
        for fname in sorted(files):
            fpath = root_path / fname
            if fname in artifact_buckets:
                with open(fpath, "r", encoding="utf-8") as f:
                    _add_if_valid(artifact_buckets[fname], json.load(f))
            elif fname == "outputs.zip":
                try:
                    with zipfile.ZipFile(fpath, "r") as zf:
                        names = set(zf.namelist())
                        for key, bucket in artifact_buckets.items():
                            if key not in file_set and key in names:
                                _add_if_valid(bucket, json.loads(zf.read(key)))
                except zipfile.BadZipFile:
                    pass

    return fi_payloads, tvla_payloads


def invalidate_stale_repo_targets(
    state: Dict[str, Any], repo_root: Path, now_iso: str
) -> None:
    """Invalidates any stored targets whose .s files changed in repo_root."""
    for group_key in ("fi_targets", "tvla_targets"):
        targets = state.get(group_key, {})
        stale = [
            (name, reason)
            for name, entry in targets.items()
            for reason in [
                check_invalidation_reason(
                    entry,
                    None,
                    compute_source_hashes(
                        repo_root, entry.get("dwarf_map", {})
                    ),
                )
            ]
            if reason is not None
        ]
        for target_name, reason in stale:
            print(f"Invalidating {target_name} ({reason})")
            del targets[target_name]
            state.setdefault("invalidation_log", []).append({
                "timestamp": now_iso,
                "target": target_name,
                "reason": reason,
            })


def _get_or_reset_target(
    state: Dict[str, Any],
    group_key: str,
    payload: Dict[str, Any],
    repo_root: Path,
    now_iso: str,
    defaults: Dict[str, Any],
) -> Dict[str, Any]:
    """Retrieves target state or creates/resets it if ELF or .s files changed."""
    target = payload.get("target") or payload.get("elf", "unknown_target")
    elf_sha256 = payload.get("elf_sha256", "")
    dwarf_map = payload.get("dwarf_map", {})
    src_hashes = compute_source_hashes(repo_root, dwarf_map)

    targets = state.setdefault(group_key, {})
    existing = targets.get(target)
    reset_reason = None

    if existing is not None:
        reset_reason = check_invalidation_reason(
            existing, elf_sha256, src_hashes
        )
        if reset_reason is not None:
            print(f"Resetting {target}: {reset_reason}")
            state.setdefault("invalidation_log", []).append({
                "timestamp": now_iso,
                "target": target,
                "reason": reset_reason,
            })
            existing = None

    if existing is None:
        existing = {
            "target": target,
            "elf": payload.get("elf", ""),
            "elf_sha256": elf_sha256,
            "source_hashes": src_hashes,
            "dwarf_map": dwarf_map,
            "runs_merged": 0,
            "last_reset_at": now_iso,
            "last_reset_reason": reset_reason or "Initial baseline",
            **defaults,
        }
        targets[target] = existing

    existing["runs_merged"] += 1
    existing["updated_at"] = now_iso
    return existing


def merge_fi_payload(
    state: Dict[str, Any],
    payload: Dict[str, Any],
    repo_root: Path,
    now_iso: str,
) -> None:
    """Merges a single FI run payload into state, resetting if changed."""
    entry = _get_or_reset_target(
        state,
        "fi_targets",
        payload,
        repo_root,
        now_iso,
        defaults={
            "attack_mode": payload.get("attack_mode", ""),
            "pc_counts": {
                str(k): int(v) for k, v in payload.get("pc_counts", {}).items()
            },
            "results": {},
        },
    )

    results = entry["results"]
    for pc_str, occ_dict in payload.get("results", {}).items():
        pc_bucket = results.setdefault(str(pc_str), {})
        for occ_str, is_vuln in occ_dict.items():
            prev = pc_bucket.get(str(occ_str), False)
            pc_bucket[str(occ_str)] = bool(prev or is_vuln)


def merge_tvla_payload(
    state: Dict[str, Any],
    payload: Dict[str, Any],
    repo_root: Path,
    now_iso: str,
) -> None:
    """Merges a single TVLA run payload into state, resetting if changed."""
    entry = _get_or_reset_target(
        state,
        "tvla_targets",
        payload,
        repo_root,
        now_iso,
        defaults={
            "t_threshold": float(payload.get("t_threshold", 6.0)),
            "counts": {},
            "sums": {},
            "sum_sqs": {},
        },
    )

    counts, sums, sum_sqs = entry["counts"], entry["sums"], entry["sum_sqs"]
    new_sums = payload.get("sums", {})
    new_sum_sqs = payload.get("sum_sqs", {})

    for pc_str, occ_map in payload.get("counts", {}).items():
        pc_c = counts.setdefault(str(pc_str), {})
        pc_s = sums.setdefault(str(pc_str), {})
        pc_q = sum_sqs.setdefault(str(pc_str), {})

        for occ_str, c_pair in occ_map.items():
            occ_key = str(occ_str)
            if occ_key not in pc_c:
                pc_c[occ_key] = [0, 0]
                pc_s[occ_key] = [[0] * NUM_MODELS, [0] * NUM_MODELS]
                pc_q[occ_key] = [[0] * NUM_MODELS, [0] * NUM_MODELS]

            s_pair = new_sums[pc_str][occ_str]
            q_pair = new_sum_sqs[pc_str][occ_str]

            for set_idx in (0, 1):
                pc_c[occ_key][set_idx] += int(c_pair[set_idx])
                for m in range(NUM_MODELS):
                    pc_s[occ_key][set_idx][m] += int(s_pair[set_idx][m])
                    pc_q[occ_key][set_idx][m] += int(q_pair[set_idx][m])


def build_dashboard_data(
    state: Dict[str, Any], repo_root: Path, commit: str
) -> Dict[str, Any]:
    """Projects per-(target, PC, occ) state onto .s source lines."""
    file_lines: Dict[str, Dict[int, Dict[str, Any]]] = {}
    all_source_files = set()

    def get_line_entry(filepath: str, lineno: int) -> Dict[str, Any]:
        filepath = normalize_source_path(filepath)
        all_source_files.add(filepath)
        return file_lines.setdefault(filepath, {}).setdefault(
            lineno,
            {
                "fi_total": 0,
                "fi_tested": 0,
                "fi_vuln": 0,
                "fi_targets": [],
                "tvla_traces": 0,
                "tvla_max_t": 0.0,
                "tvla_threshold": 6.0,
                "tvla_leaking": False,
                "tvla_worst_model": "",
                "tvla_targets": [],
            },
        )

    # 1. Project FI targets onto (filepath, lineno)
    for target_name, entry in sorted(state.get("fi_targets", {}).items()):
        dwarf_map = entry.get("dwarf_map", {})
        results = entry.get("results", {})

        for pc_str, raw_count in entry.get("pc_counts", {}).items():
            loc = dwarf_map.get(str(pc_str))
            if not loc or len(loc) < 2:
                continue
            line_entry = get_line_entry(str(loc[0]), int(loc[1]))

            targetable = min(MAX_PC_DEPTH, int(raw_count))
            occ_results = results.get(str(pc_str), {})
            tested = len(occ_results)
            vuln = sum(1 for v in occ_results.values() if v)

            line_entry["fi_total"] += targetable
            line_entry["fi_tested"] += tested
            line_entry["fi_vuln"] += vuln
            line_entry["fi_targets"].append({
                "target": target_name,
                "pc": f"0x{int(pc_str):04x}",
                "tested": tested,
                "total": targetable,
                "vuln": vuln,
                "attack_mode": entry.get("attack_mode", ""),
            })

    # 2. Project TVLA targets onto (filepath, lineno)
    tvla_target_stats: Dict[str, Tuple[int, float]] = {}
    for target_name, entry in sorted(state.get("tvla_targets", {}).items()):
        dwarf_map = entry.get("dwarf_map", {})
        threshold = float(entry.get("t_threshold", 6.0))
        acc = TVLAAccumulator()
        acc.counts = entry.get("counts", {})
        acc.sums = entry.get("sums", {})
        acc.sum_sqs = entry.get("sum_sqs", {})

        target_leaking_pcs = 0
        target_max_t = 0.0

        for pc_str, occ_map in acc.counts.items():
            pc_max_t = 0.0
            pc_worst_model = ""
            pc_traces = 0
            pc_leaking = False

            for occ_str, c_pair in occ_map.items():
                pc_traces = max(pc_traces, int(c_pair[0]) + int(c_pair[1]))
                for m in range(NUM_MODELS):
                    t_val = abs(acc.compute_t_test(pc_str, occ_str, m))
                    if t_val >= pc_max_t:
                        pc_max_t = t_val
                        pc_worst_model = MODEL_NAMES.get(m, f"M{m}")
                    if t_val > threshold:
                        pc_leaking = True

            target_max_t = max(target_max_t, pc_max_t)
            if pc_leaking:
                target_leaking_pcs += 1

            loc = dwarf_map.get(str(pc_str))
            if not loc or len(loc) < 2:
                continue
            line_entry = get_line_entry(str(loc[0]), int(loc[1]))

            line_entry["tvla_traces"] = max(
                line_entry["tvla_traces"], pc_traces
            )
            if pc_max_t >= line_entry["tvla_max_t"]:
                line_entry["tvla_max_t"] = round(pc_max_t, 2)
                line_entry["tvla_threshold"] = threshold
                line_entry["tvla_worst_model"] = pc_worst_model
            if pc_leaking:
                line_entry["tvla_leaking"] = True

            line_entry["tvla_targets"].append({
                "target": target_name,
                "pc": f"0x{int(pc_str):04x}",
                "traces": pc_traces,
                "max_t": round(pc_max_t, 2),
                "threshold": threshold,
                "worst_model": pc_worst_model,
                "leaking": pc_leaking,
            })

        tvla_target_stats[target_name] = (target_leaking_pcs, target_max_t)

    # 3. Assemble file records with source lines and line-by-line status
    files_out: Dict[str, Any] = {}
    for filepath in sorted(all_source_files):
        full_path = repo_root / filepath
        if full_path.is_file():
            raw_lines = full_path.read_text(encoding="utf-8").splitlines()
            file_sha = compute_file_sha256(full_path) or ""
        else:
            raw_lines = [f"// Source file not found at {filepath}"]
            file_sha = ""

        serialized_lines: Dict[str, Any] = {}
        for lineno, info in sorted(file_lines.get(filepath, {}).items()):
            if info["fi_vuln"] > 0 or info["tvla_leaking"]:
                status = "fail"
            elif info["fi_tested"] > 0 or info["tvla_traces"] >= 4:
                status = "pass"
            else:
                status = "untested"
            serialized_lines[str(lineno)] = {"status": status, **info}

        vals = list(serialized_lines.values())
        files_out[filepath] = {
            "sha256": file_sha,
            "source_lines": raw_lines,
            "summary": {
                "exec_lines": len(vals),
                "pass_lines": sum(1 for v in vals if v["status"] == "pass"),
                "fail_lines": sum(1 for v in vals if v["status"] == "fail"),
                "untested_lines": sum(
                    1 for v in vals if v["status"] == "untested"
                ),
                "fi_total": sum(v["fi_total"] for v in vals),
                "fi_tested": sum(v["fi_tested"] for v in vals),
                "fi_vuln": sum(v["fi_vuln"] for v in vals),
                "tvla_max_t": round(
                    max((v["tvla_max_t"] for v in vals), default=0.0), 2
                ),
                "tvla_traces": max(
                    (v["tvla_traces"] for v in vals), default=0
                ),
            },
            "lines": serialized_lines,
        }

    # 4. Target summaries
    targets_summary: List[Dict[str, Any]] = []
    for name, entry in sorted(state.get("fi_targets", {}).items()):
        pc_counts = entry.get("pc_counts", {})
        results = entry.get("results", {})
        tot = sum(min(MAX_PC_DEPTH, int(c)) for c in pc_counts.values())
        tst = sum(len(occs) for occs in results.values())
        vln = sum(
            sum(1 for v in occs.values() if v) for occs in results.values()
        )
        targets_summary.append({
            "target": name,
            "kind": "FI",
            "elf": entry.get("elf", ""),
            "elf_sha256": entry.get("elf_sha256", "")[:12],
            "runs_merged": entry.get("runs_merged", 0),
            "progress": f"{tst}/{tot} skips ({100.0 * tst / max(1, tot):.1f}%)",
            "findings": f"{vln} fault(s)",
            "last_reset_at": entry.get("last_reset_at", ""),
            "last_reset_reason": entry.get("last_reset_reason", ""),
        })

    for name, entry in sorted(state.get("tvla_targets", {}).items()):
        counts = entry.get("counts", {})
        traces = 0
        if counts:
            first_occ = next(iter(next(iter(counts.values())).values()))
            traces = int(first_occ[0]) + int(first_occ[1])
        leaking_pcs, target_max_t = tvla_target_stats.get(name, (0, 0.0))
        targets_summary.append({
            "target": name,
            "kind": "TVLA",
            "elf": entry.get("elf", ""),
            "elf_sha256": entry.get("elf_sha256", "")[:12],
            "runs_merged": entry.get("runs_merged", 0),
            "progress": f"{traces} traces",
            "findings": f"{leaking_pcs} leak(s) (max |t|={target_max_t:.2f})",
            "last_reset_at": entry.get("last_reset_at", ""),
            "last_reset_reason": entry.get("last_reset_reason", ""),
        })

    return {
        "metadata": {
            "updated_at": state.get("updated_at", ""),
            "commit": commit or state.get("commit", ""),
            "invalidation_log": (
                state.get("invalidation_log", [])[-MAX_INVALIDATION_LOG:]
            ),
        },
        "targets": targets_summary,
        "files": files_out,
    }


def bundle_viewer_html(
    dashboard_data: Dict[str, Any],
    template_path: Path,
    output_html_path: Path,
) -> None:
    """Bundles gzipped dashboard JSON into standalone HTML viewer."""
    template = template_path.read_text(encoding="utf-8")
    gz_bytes = gzip.compress(
        json.dumps(dashboard_data).encode("utf-8"), compresslevel=9
    )
    b64_payload = base64.b64encode(gz_bytes).decode("ascii")

    placeholder = "/* == PANOPTICON_BUNDLED_DATA == */"
    if placeholder not in template:
        raise ValueError(f"Placeholder {placeholder!r} missing in {template_path}")

    rendered = template.replace(
        placeholder, f'const BUNDLED_DATA_B64 = "{b64_payload}";', 1
    )
    output_html_path.parent.mkdir(parents=True, exist_ok=True)
    output_html_path.write_text(rendered, encoding="utf-8")


def run_pipeline(
    state_file: Path,
    input_dir: Path,
    repo_root: Path,
    output_html: Path,
    viewer_template: Path,
    commit: str = "",
) -> Dict[str, Any]:
    """Runs the full invalidation, aggregation, and report bundling pipeline."""
    now_iso = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    state = load_state(state_file)
    state["updated_at"] = now_iso
    if commit:
        state["commit"] = commit

    invalidate_stale_repo_targets(state, repo_root, now_iso)

    fi_payloads, tvla_payloads = discover_artifacts(input_dir)
    print(
        f"Discovered {len(fi_payloads)} FI artifacts and "
        f"{len(tvla_payloads)} TVLA artifacts in {input_dir}"
    )

    for payload in fi_payloads:
        merge_fi_payload(state, payload, repo_root, now_iso)
    for payload in tvla_payloads:
        merge_tvla_payload(state, payload, repo_root, now_iso)

    state["invalidation_log"] = state.get("invalidation_log", [])[
        -MAX_INVALIDATION_LOG:
    ]
    save_state(state, state_file)

    dashboard_data = build_dashboard_data(state, repo_root, commit)
    bundle_viewer_html(dashboard_data, viewer_template, output_html)
    print(f"Bundled standalone Panopticon viewer at {output_html}")

    return dashboard_data


def main(argv: Optional[Iterable[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Aggregate OTBN Panopticon FI/TVLA runs and render viewer."
    )
    parser.add_argument(
        "--state-file",
        type=Path,
        required=True,
        help="Path to cumulative state file (.json or .json.gz).",
    )
    parser.add_argument(
        "--input-dir",
        type=Path,
        default=Path("bazel-testlogs"),
        help="Directory to scan for fi_results.json & tvla_accumulators.json.",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path("."),
        help="Path to OpenTitan repository root for reading .s files.",
    )
    parser.add_argument(
        "--viewer-template",
        type=Path,
        default=Path(__file__).parent / "viewer.html",
        help="Path to viewer.html template.",
    )
    parser.add_argument(
        "--output-html",
        type=Path,
        required=True,
        help="Output path for standalone bundled HTML report.",
    )
    parser.add_argument(
        "--commit",
        type=str,
        default="",
        help="Git commit SHA for report metadata.",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    run_pipeline(
        state_file=args.state_file,
        input_dir=args.input_dir,
        repo_root=args.repo_root,
        output_html=args.output_html,
        viewer_template=args.viewer_template,
        commit=args.commit,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
