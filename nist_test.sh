#!/bin/bash
# Copyright 2019 The ChromiumOS Authors
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# NIST toolset needs sudo emerge dev-libs/libdivsufsort and bz2
# apt-get install libbz2-dev libdivsufsort-dev libjsoncpp-dev libssl-dev libmpfr-dev
set -e
TMP_PATH="nist_entropy"
NIST_URL="https://github.com/usnistgov/SP800-90B_EntropyAssessment.git"
TRNG_OUT="$1"
TRNG_OUT_RESTART="$1""_restart"
EA_LOG="ea_non_iid.log"
echo Using ${TRNG_OUT} and ${TRNG_OUT_RESTART}
#rm -rf "${TMP_PATH}"
if [ ! -f "${TMP_PATH}/cpp/ea_non_iid" ];then
git clone --depth 1 "${NIST_URL}" "${TMP_PATH}" || true
# build entropy assessment tool using mode for non independent and identically
# distributed data, as for  H1 TRNG we can't justify the oppposite
make -j -C "${TMP_PATH}/cpp/" non_iid restart
fi
rm -f "${EA_LOG}"
"${TMP_PATH}/cpp/ea_non_iid" -v -a "${TRNG_OUT}" | tee "${EA_LOG}"
entropy="$(awk '/min/ {print $5}' "${EA_LOG}")"
if [[ -z "${entropy}" ]]; then
    entropy="$(awk '/H_original/ {print $2}' "${EA_LOG}")"
fi
echo "Minimal entropy ${entropy}"
"${TMP_PATH}/cpp/ea_restart" -v "${TRNG_OUT_RESTART}" \
    "${entropy}" | tee -a "${EA_LOG}"
