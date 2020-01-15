#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This script installs Verible, an open-source style lint and code
# formatting tool: https://github.com/google/verible
# Note that this tool is still experimental. Especially the formatting
# part is still under active development, and hence not production ready.
#

VERIBLE_VERSION=e654c18e4e712285757f9667f737a73f88f71c01
INSTALL_DIR=/tools/verible

# this requires the bazel build system and GCC7
# see https://docs.bazel.build/versions/master/install-ubuntu.html

echo "checking whether bazel is installed..."
if which bazel; then
	echo "OK"
else
	echo "bazel is not installed. installing bazel..."
	sudo apt install curl -y
	curl https://bazel.build/bazel-release.pub.gpg | sudo apt-key add -
	echo "deb [arch=amd64] https://storage.googleapis.com/bazel-apt stable jdk1.8" \
		| sudo tee /etc/apt/sources.list.d/bazel.list
	sudo apt update && sudo apt install bazel -y
fi

# upgrade to GCC7
# TODO: check whether we need to maintain the default symlinks here
# for gcc -> GCC-5* such that other tools still work.
echo "checking whether GCC7 is installed..."
if which gcc-7; then
	echo "OK"
else
	echo "GCC7 is not installed. installing GCC7..."
	sudo add-apt-repository ppa:ubuntu-toolchain-r/test
	sudo apt update
	sudo apt install g++-7 -y
fi

# get verible and install under /tools/verible
# note: you may add $INSTALL_DIR to the PATH, but it is not
# required for the run scripts to work.
echo "Installing Verible ($VERIBLE_VERSION)..."

mkdir -p build && cd build
git clone https://github.com/google/verible.git
cd verible
git checkout $VERIBLE_VERSION

bazel build --cxxopt='-std=c++17' //...
bazel test --cxxopt='-std=c++17' //...

sudo mkdir -p $INSTALL_DIR

sudo install bazel-bin/verilog/tools/syntax/verilog_syntax $INSTALL_DIR
sudo install bazel-bin/verilog/tools/formatter/verilog_format $INSTALL_DIR
sudo install bazel-bin/verilog/tools/lint/verilog_lint $INSTALL_DIR

echo "done"


