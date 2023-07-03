#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
##########################################################
#
# Utility tasks that may be run after building the site (build-docs.sh)
# but before deploying (cloudbuild-deploy-docs.yaml/deploy.sh)
#
##########################################################

set -e

# Get the project directory from the location of this script
this_dir=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
proj_root=$( realpath "${this_dir}/../.." )
build_dir="${proj_root}/build-site"

# Check for brotli
if ! command -v brotli >/dev/null; then
    echo "E: brotli not found." >&2
    exit 1
fi

############
# BUILDING #
############

compress_br_inplace () {
    # Compress the searchindex.json files (which are large, hence worth compressing here.)
    search_indexes=$(find "${build_dir}" -type f -name '*searchindex.json')
    for f in $search_indexes; do
        echo "Compressing ${f}"
        # When serving from gcloud buckets, file should be uploaded with an identical name as the
        # original, but compressed and with the matching 'content-encoding' tag applied.
        cp "${f}" "${f}.orig"
        brotli "${f}"
        mv "${f}.br" "${f}"
        # Log the resulting improvement
        du -h "${f}.orig"
        du -h "${f}"
    done
}

#######
# CLI #
#######
case "$1" in
    "compress_br") compress_br_inplace ;;
    "help"|*)
        echo "USAGE: $0 <command>"
        echo ""
        echo "commands:"
        echo "  help             prints this message."
        echo "  compress_br      compresses using brotli in-place, replacing the existing files"
        exit 0
        ;;
esac
