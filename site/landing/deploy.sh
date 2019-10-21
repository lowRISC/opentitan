#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

TARGET=$1

case "${TARGET}" in
  "public" | "staging")
    ;;

  *)
    echo "You must specify either \"public\" or \"staging\""
    exit 1
    ;;
esac

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd $DIR
rm -rf public

hugo --minify
hugo deploy --target "${TARGET}" --confirm --verbose --maxDeletes -1

if [ "${TARGET}" = "public" ]; then
  # TODO: The ability to invalidate a Cloud CDN cache is pending in upstream
  # hugo.  Once it's landed this can be rolled into the hugo configuration.
  gcloud compute url-maps invalidate-cdn-cache "opentitan-dot-org" --path="/*" \
    --async
fi
