#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

TARGET=$1

case "${TARGET}" in
  "docs")
    PROJECT=active-premise-257318
    INSTANCE_GROUP=docs-redirector
    ;;

  "landing")
    PROJECT=gold-hybrid-255313
    INSTANCE_GROUP=opentitan-dot-org-redirector
    ;;

  *)
    echo "You must specify either \"docs\" or \"landing\""
    exit 1
    ;;
esac

gcloud --project="${PROJECT}" builds submit \
  --tag "gcr.io/${PROJECT}/redirector" .
gcloud --project="${PROJECT}" compute instance-groups managed \
  rolling-action replace --max-surge=3 --region=us-central1 "${INSTANCE_GROUP}"
