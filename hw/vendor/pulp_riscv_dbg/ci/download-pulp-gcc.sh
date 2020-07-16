#!/bin/bash
set -o pipefail
set -e

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="v1.0.16"

# mkdir -p $RISCV

wget https://github.com/pulp-platform/pulp-riscv-gnu-toolchain/releases/download/$VERSION/$VERSION-pulp-riscv-gcc-ubuntu-16.tar.bz2
echo "unpacking pulp gcc and installing to $RISCV"
tar -xvf $VERSION-pulp-riscv-gcc-ubuntu-16.tar.bz2 -C "$RISCV" --strip 1
