#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage()
{
    echo "Usage: install-package-dependencies.sh --verilator-version V"
    # TODO: Remove vestigial `--verible-version` flag once the "CI (private)"
    # pipeline stops passing it.
    echo "                                       --verible-version V"
    exit 1
}

error()
{
    echo >&2 "$@"
    exit 1
}

long="verilator-version:,verible-version:"
ARGS="$(getopt -o "" -l "$long" -- "$@")" || usage

VERILATOR_VERSION=

eval set -- "$ARGS"
while :
do
    case "$1" in
        --verilator-version) VERILATOR_VERSION="$2"; shift 2 ;;
        --verible-version) echo "##[warning]Ignoring deprecated flag: --verible-version"; shift 2 ;;
        --) shift; break ;;
        *)  error "getopt / case statement mismatch"
    esac
done

# Check that we've seen all the expected versions
test -n "$VERILATOR_VERSION" || error "Missing --verilator-version"

# Check that there aren't any positional arguments
test $# = 0 || error "Unexpected positional arguments"

CI_DIR="$(dirname "$(readlink -e "${BASH_SOURCE[0]}")")"
REPO_TOP="$(readlink -e "$CI_DIR/..")"

cd "$REPO_TOP"

# Use apt-fast if available for faster installation.
if command -v apt-fast >/dev/null; then
  APT_CMD=apt-fast
else
  APT_CMD=apt-get
fi

TMPDIR="$(mktemp -d)" || {
    error "Failed to create temporary directory"
}
trap 'rm -rf "$TMPDIR"' EXIT

# Install gcc-9 and set it as the default.
sudo add-apt-repository ppa:ubuntu-toolchain-r/test \
  && sudo $APT_CMD update \
  && sudo $APT_CMD install -y gcc-9 g++-9 \
  && sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-9 90 \
  && sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-9 90 || {
    error "Failed to set up gcc-9"
  }

# Ensure apt package index is up-to-date.
sudo $APT_CMD update || {
    error "Failed to run apt update"
}

ci_reqs="$TMPDIR/apt-requirements-ci.txt"
cp apt-requirements.txt "$ci_reqs"
echo rsync >> "$ci_reqs"

# NOTE: We use sed to remove all comments from apt-requirements-ci.txt,
# since apt-get/apt-fast doesn't actually provide such a feature.
sed -i -e '/^$/d' -e '/^#/d' -e 's/#.*//' "$ci_reqs"

echo "Amended apt-requirements:"
cat "$ci_reqs"

xargs sudo $APT_CMD install -y <"$ci_reqs"

# Python requirements are installed to the local user directory so prepend
# appropriate bin directory to the PATH
export PATH=$HOME/.local/bin:$PATH

python3 -m pip install --user -r python-requirements.txt --require-hashes

# Install verilator
lsb_sr="$(lsb_release -sr)"
if [ $lsb_sr = "18.04" ]; then
  UBUNTU_SUFFIX="-u18"
fi

VERILATOR_TARBALL=verilator"$UBUNTU_SUFFIX-v$VERILATOR_VERSION".tar.gz
VERILATOR_URL=https://storage.googleapis.com/verilator-builds/$VERILATOR_TARBALL
echo "Fetching verilator tarball" $VERILATOR_URL
curl -f -Ls -o "$VERILATOR_TARBALL" "$VERILATOR_URL" || {
    error "Failed to download verilator from ${VERILATOR_URL}"
}

sudo mkdir -p /tools/verilator
sudo chmod 777 /tools/verilator
tar -C /tools/verilator -xvzf $VERILATOR_TARBALL
export PATH=/tools/verilator/v$VERILATOR_VERSION/bin:$PATH

# Propagate PATH changes to all subsequent steps of the job
echo "##vso[task.setvariable variable=PATH]$PATH"
