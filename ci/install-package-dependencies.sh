#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

usage()
{
    echo "Usage: install-package-dependencies.sh --verilator-version V"
    echo "                                       --verible-version V"
    echo "                                       --rust-version V"
    exit 1
}

error()
{
    echo >&2 "$@"
    exit 1
}

long="verilator-version:,verible-version:,rust-version:"
ARGS="$(getopt -o "" -l "$long" -- "$@")" || usage

VERILATOR_VERSION=
VERIBLE_VERSION=

eval set -- "$ARGS"
while :
do
    case "$1" in
        --verilator-version) VERILATOR_VERSION="$2"; shift 2 ;;
        --verible-version)   VERIBLE_VERSION="$2";   shift 2 ;;
        --rust-version)      RUST_VERSION="$2";      shift 2 ;;
        --) shift; break ;;
        *)  error "getopt / case statement mismatch"
    esac
done

# Check that we've seen all the expected versions
test -n "$VERILATOR_VERSION" || error "Missing --verilator-version"
test -n "$VERIBLE_VERSION"   || error "Missing --verible-version"
test -n "$RUST_VERSION"      || error "Missing --rust-version"

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

# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
python3 -m pip install --user -U pip "setuptools<66.0.0"

pip3 install --user -r python-requirements.txt

# Install Verible
lsb_sr="$(lsb_release -sr)"
lsb_sc="$(lsb_release -sc)"
VERIBLE_BASE_URL="https://github.com/google/verible/releases/download"
VERIBLE_TARBALL="verible-${VERIBLE_VERSION}-Ubuntu-${lsb_sr}-${lsb_sc}-x86_64.tar.gz"
VERIBLE_URL="${VERIBLE_BASE_URL}/${VERIBLE_VERSION}/${VERIBLE_TARBALL}"

verible_tar="$TMPDIR/verible.tar.gz"

curl -f -Ls -o "$verible_tar" "${VERIBLE_URL}" || {
    error "Failed to download verible from ${VERIBLE_URL}"
}

sudo mkdir -p /tools/verible
sudo chmod 777 /tools/verible
tar -C /tools/verible -xf "$verible_tar" --strip-components=1
export PATH=/tools/verible/bin:$PATH

# Install verilator
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

# Install Rust
sw/vendor/rustup/rustup-init.sh -y \
    --default-toolchain "${RUST_VERSION}"
export PATH=$HOME/.cargo/bin:$PATH

# Install mdbook
MDBOOK_VERSION="v0.4.27"
MDBOOK_BASE_URL="https://github.com/rust-lang/mdBook/releases/download"
MDBOOK_TARBALL="mdbook-${MDBOOK_VERSION}-x86_64-unknown-linux-gnu.tar.gz"
MDBOOK_URL="${MDBOOK_BASE_URL}/${MDBOOK_VERSION}/${MDBOOK_TARBALL}"
MDBOOK_DOWNLOAD="$TMPDIR/mdbook.tar.gz"

curl -f -Ls -o "$MDBOOK_DOWNLOAD" "${MDBOOK_URL}" || {
    error "Failed to download verible from ${MDBOOK_URL}"
}

sudo mkdir -p /tools/mdbook
sudo chmod 777 /tools/mdbook
tar -C /tools/mdbook -xf "$MDBOOK_DOWNLOAD"
export PATH=/tools/mdbook:$PATH

# Propagate PATH changes to all subsequent steps of the job
echo "##vso[task.setvariable variable=PATH]$PATH"
