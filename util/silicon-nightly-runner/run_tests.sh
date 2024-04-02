#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
##
# Run the tests.
#

USER=$(whoami)
BRANCH=${BRANCH:-earlgrey_es_sival}
OT_HOME=../opentitan

cd $OT_HOME || exit
git checkout "${BRANCH}"
git pull --autostash

if [ -d bazel-out ] ; then
    chmod -R +w bazel-out/
    rm -rf bazel-out/
fi

./bazelisk.sh clean
./bazelisk.sh run //sw/host/opentitantool -- --interface=hyperdebug_dfu transport update-firmware
./bazelisk.sh test --//signing:token=//signing/tokens:cloud_kms_sival \
                --build_tests_only \
                --test_tag_filters="silicon_owner_sival_rom_ext" \
                $(bash ./bazelisk.sh query 'attr("tags", "[\[ ]silicon_owner_sival_rom_ext[,\]]", tests(//...))' | grep -v examples | grep -v penetrationtests) || true
cd - || exit
