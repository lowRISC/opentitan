#!/bin/bash
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/.."
[ -d tmp ] || rm -rf tmp
mkdir -p tmp
