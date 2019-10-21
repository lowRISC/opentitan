#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

gcloud builds submit --tag gcr.io/gold-hybrid-255313/redirector .
gcloud compute instance-groups managed rolling-action replace \
  --max-surge=3 --max-unavailable=1 --region=us-central1 \
  opentitan-dot-org-redirector
