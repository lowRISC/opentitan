#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Fetches remote cached artifacts from a Bazel remote cache.

This script identifies missing local files from a provided list, resolves their
corresponding hashes by dumping the Bazel action cache, and attempts to
download them from the remote cache URL.
"""

import argparse
import logging
import os
import re
import requests
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger(__name__)


def get_remote_cache_url() -> Optional[str]:
    """Resolves the remote cache URL from bazel configuration."""
    try:
        result = subprocess.run(
            ["./ci/bazelisk.sh", "config", "--announce_rc"],
            capture_output=True,
            text=True,
            check=True,
        )
        # Search for --remote_cache=URL. We take the first match found in the config.
        m = re.search(r"--remote_cache=(\S+)", result.stdout + result.stderr)
        if m:
            return m.group(1).rstrip("/")
    except subprocess.CalledProcessError:
        logger.warning("Failed to run bazelisk to resolve remote cache URL.")
    except Exception as e:
        logger.warning(f"Unexpected error resolving remote cache URL: {e}")
    return None


def get_action_cache_map() -> Dict[str, str]:
    """Parses the action cache dump and returns a mapping from path to hash."""
    try:
        result = subprocess.run(
            ["./ci/bazelisk.sh", "dump", "--action_cache"],
            capture_output=True,
            text=True,
            check=True,
        )
    except subprocess.CalledProcessError as e:
        logger.error(f"Error running bazelisk dump --action_cache: {e}")
        if e.stderr:
            logger.error(e.stderr)
        sys.exit(1)

    cache_map = {}
    # Matches: <path> = ... <SHA-256 hash>
    # We capture the path and the 64-character hex hash.
    pattern = re.compile(
        r"^\s*(?P<path>\S+)\s*=\s*.*?(?P<hash>[0-9a-fA-F]{64})")

    for line in result.stdout.splitlines():
        m = pattern.search(line)
        if m:
            cache_map[m.group("path")] = m.group("hash").lower()

    return cache_map


def fetch_artifact(path_str: str, artifact_hash: str,
                   remote_cache: str) -> bool:
    """Fetches an artifact from the remote cache and saves it to path_str."""
    path = Path(path_str)
    url = f"{remote_cache}/cas/{artifact_hash}"

    try:
        # Using a timeout to avoid hanging indefinitely
        response = requests.get(url, stream=True, timeout=30)
        if response.status_code == 200:
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("wb") as f:
                for chunk in response.iter_content(chunk_size=8192):
                    f.write(chunk)
            logger.info(f"Fetched {path_str}")
            return True
        elif response.status_code == 404:
            logger.warning(
                f"Artifact not found in cache: {path_str} ({artifact_hash})")
        else:
            logger.error(
                f"Failed to fetch {path_str}: HTTP {response.status_code}")
    except requests.exceptions.RequestException as e:
        logger.error(f"Error fetching {path_str} from {url}: {e}")
    return False


def main():
    parser = argparse.ArgumentParser(
        description=
        "Fetch missing remote cached artifacts from a list of paths.")
    parser.add_argument(
        "--remote_cache",
        help=
        "Remote cache URL. If not provided, resolves from bazelisk config.",
    )
    parser.add_argument(
        "--file-list",
        help=
        "File containing list of file paths to fetch. If not provided, reads from stdin."
    )
    args = parser.parse_args()

    # Gather all paths from input source
    if args.file_list:
        logger.info(f"Reading file list from {args.file_list}")
        with open(args.file_list, "r") as f:
            paths = [line.strip() for line in f if line.strip()]
    else:
        logger.info("Reading file list from stdin")
        paths = [line.strip() for line in sys.stdin if line.strip()]

    # Pre-check: identify missing files
    missing_paths = [p for p in paths if not os.path.exists(p)]
    if not missing_paths:
        logger.info("All files already exist locally. Nothing to fetch.")
        return
    logger.info(f"Found {len(missing_paths)} missing files to fetch.")

    # Resolve remote cache URL only if there are missing files
    remote_cache = args.remote_cache or get_remote_cache_url()
    if not remote_cache:
        parser.error(
            "--remote_cache not provided and could not be resolved from config."
        )

    remote_cache = remote_cache.rstrip("/")
    logger.info(f"Using remote cache: {remote_cache}")

    # Load action cache map
    cache_map = get_action_cache_map()
    logger.info(f"Loaded {len(cache_map)} entries from action cache.")

    # Process missing file paths
    for path_str in missing_paths:
        artifact_hash = cache_map.get(path_str)
        if artifact_hash:
            fetch_artifact(path_str, artifact_hash, remote_cache)
        else:
            logger.warning(f"No cache entry found for {path_str}")


if __name__ == "__main__":
    main()
