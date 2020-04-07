#!/bin/bash
#
# Copyright 2019 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

VERIBLE_VERSION=751d4d8e57741ab22806f91982f59c71ecf37d9d
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
  echo "Error: GCC7 is not installed. Exit and Verible isn't installed"
  exit 0
fi

# get verible and install under /tools/verible
# note: you may add $INSTALL_DIR to the PATH, but it is not
# required for the run scripts to work.
echo "Installing Verible ($VERIBLE_VERSION)..."

mkdir -p build && cd build
git clone https://github.com/google/verible.git
cd verible
git pull origin master
git checkout $VERIBLE_VERSION

bazel build --cxxopt='-std=c++17' //...
bazel test --cxxopt='-std=c++17' //...

sudo mkdir -p $INSTALL_DIR

sudo install bazel-bin/verilog/tools/syntax/verilog_syntax $INSTALL_DIR
sudo install bazel-bin/verilog/tools/formatter/verilog_format $INSTALL_DIR
sudo install bazel-bin/verilog/tools/lint/verilog_lint $INSTALL_DIR

echo "done"


