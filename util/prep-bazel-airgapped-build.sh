#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

: "${REPO_TOP:=$(git rev-parse --show-toplevel)}"

: "${BAZELISK:=${REPO_TOP}/bazelisk.sh}"
: "${BAZEL_VERSION:=$(cat "${REPO_TOP}/.bazelversion")}"

: "${BAZEL_AIRGAPPED_DIR:=${REPO_TOP}/bazel-airgapped}"
: "${BAZEL_CACHEDIR:=${BAZEL_AIRGAPPED_DIR}/bazel-cache}"
: "${BAZEL_VENDORDIR:=${BAZEL_AIRGAPPED_DIR}/bazel-vendor}"
: "${BAZEL_BITSTREAMS_CACHE:=${BAZEL_AIRGAPPED_DIR}/bitstreams-cache}"
: "${BAZEL_BITSTREAMS_CACHEDIR:=${BAZEL_BITSTREAMS_CACHE}/cache}"

LINE_SEP="====================================================================="

################################################################################
# Process cmd line args.
################################################################################
usage() {
  cat << USAGE
Utility script to prepare a directory with all bazel dependencies needed to
build project artifacts with bazel in an airgapped environment.

Usage: $0 [-c ALL | BAZEL | VENDOR]

  - c: airgapped directory contents, set to either ALL, BAZEL, or VENDOR.
  - f: force rebuild of airgapped directory, overwriting any existing one.

Airgapped directory contents (-c):
  - ALL: both the bazel binary and vendor dir will be added. (Default)
  - BAZEL: only the bazel binary will be added.
  - VENDOR: only the OpenTitan bazel mod dependencies will be added.

USAGE
}

AIRGAPPED_DIR_CONTENTS="ALL"
FORCE_REBUILD=false

while getopts ':c:f' flag; do
  case "${flag}" in
    c) AIRGAPPED_DIR_CONTENTS="${OPTARG}";;
    f) FORCE_REBUILD=true;;
    \?) echo "Unexpected option: -${OPTARG}" >&2
        usage
        exit 1
        ;;
    :) echo "Option -${OPTARG} requires an argument" >&2
       usage
       exit 1
       ;;
    *) echo "Internal Error: Unhandled option: -${flag}" >&2
       exit 1
       ;;
  esac
done
shift $((OPTIND - 1))

# We do not accept additional arguments.
if [[ "$#" -gt 0 ]]; then
  echo "Unexpected arguments:" "$@" >&2
  exit 1
fi

if [[ ${AIRGAPPED_DIR_CONTENTS} != "ALL" && \
      ${AIRGAPPED_DIR_CONTENTS} != "BAZEL" && \
      ${AIRGAPPED_DIR_CONTENTS} != "VENDOR" ]]; then
  echo "Invalid -c option: ${AIRGAPPED_DIR_CONTENTS}." >&2
  echo "Expected ALL, BAZEL, or VENDOR." >&2
  exit 1
fi


################################################################################
# Check if a previous airgapped directory has been built.
################################################################################
if [[ -d ${BAZEL_AIRGAPPED_DIR} ]]; then
  if [[ ${FORCE_REBUILD} = false ]]; then
    while true; do
      read -p "Airgapped directory exists, rebuild? [Y/n]" yn
      case $yn in
          "") rm -rf ${BAZEL_AIRGAPPED_DIR}; break;;
          [Yy]*) rm -rf ${BAZEL_AIRGAPPED_DIR}; break;;
          [Nn]*) exit;;
          *) echo "Please enter [Yy] or [Nn]."
      esac
    done
  else
    rm -rf ${BAZEL_AIRGAPPED_DIR}
  fi
fi

################################################################################
# Setup the airgapped directory.
################################################################################
mkdir -p ${BAZEL_AIRGAPPED_DIR}

################################################################################
# Download bazel.
################################################################################
if [[ ${AIRGAPPED_DIR_CONTENTS} == "ALL" || \
      ${AIRGAPPED_DIR_CONTENTS} == "BAZEL" ]]; then
  echo $LINE_SEP
  echo "Downloading bazel ..."
  pushd ${BAZEL_AIRGAPPED_DIR}
  curl --silent --location \
    https://github.com/bazelbuild/bazel/releases/download/${BAZEL_VERSION}/bazel-${BAZEL_VERSION}-linux-x86_64 \
    --output bazel
  chmod +x bazel
  popd
fi

################################################################################
# Prepare the cache.
################################################################################
if [[ ${AIRGAPPED_DIR_CONTENTS} == "ALL" || \
      ${AIRGAPPED_DIR_CONTENTS} == "VENDOR" ]]; then
  echo $LINE_SEP
  echo "Preparing bazel offline vendor_dir ..."
  cd ${REPO_TOP}
  mkdir -p ${BAZEL_CACHEDIR}
  # Make bazel forget everything it knows, then download everything.
  ${BAZELISK} clean --expunge
  ${BAZELISK} vendor --vendor_dir="${BAZEL_VENDORDIR}" //...
  # We don't need all bitstreams in the cache, we just need the latest one so
  # that the cache is "initialized" and "offline" mode will work correctly.
  mkdir -p ${BAZEL_BITSTREAMS_CACHEDIR}
  readonly SYSTEM_BITSTREAM_CACHE="${HOME}/.cache/opentitan-bitstreams"
  readonly SYSTEM_BITSTREAM_CACHEDIR="${SYSTEM_BITSTREAM_CACHE}/cache"
  readonly LATEST_BITSTREAM_HASH_FILE="${SYSTEM_BITSTREAM_CACHE}/latest.txt"
  # Ensure the system bitstream cache is populated. If latest.txt is missing,
  # fetch it from GCP. If the bitstream files for the recorded hash are missing,
  # fetch that specific revision. Skip network access when both are present.
  if [[ ! -f "${LATEST_BITSTREAM_HASH_FILE}" ]]; then
    BITSTREAM="latest" ${BAZELISK} fetch @bitstreams//...
  else
    _latest_hash=$(cat "${LATEST_BITSTREAM_HASH_FILE}")
    if [[ ! -d "${SYSTEM_BITSTREAM_CACHEDIR}/${_latest_hash}" ]]; then
      BITSTREAM="${_latest_hash}" ${BAZELISK} fetch @bitstreams//...
    fi
    unset _latest_hash
  fi
  cp "${LATEST_BITSTREAM_HASH_FILE}" \
    "${BAZEL_BITSTREAMS_CACHE}/"
  LATEST_BITSTREAM_HASH=$(cat "${LATEST_BITSTREAM_HASH_FILE}")
  cp -r "${SYSTEM_BITSTREAM_CACHEDIR}/${LATEST_BITSTREAM_HASH}" \
    "${BAZEL_BITSTREAMS_CACHEDIR}"
  echo "Done."
fi

################################################################################
# Print some usage instructions.
################################################################################
if [[ ${AIRGAPPED_DIR_CONTENTS} == "ALL" ]]; then
  echo $LINE_SEP
  echo "To perform an airgapped build, ship the contents of ${BAZEL_AIRGAPPED_DIR} to your airgapped environment and then:"
  echo ""
  echo "bazel build --vendor_dir=${BAZEL_VENDORDIR} <target>"
fi
