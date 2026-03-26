#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

NGINX_CONF="$(pwd)/ci/scripts/nginx-bazel-cache-overlay.conf"
CACHE_DIR="/tmp/bazel-cache"

mkdir -p "${CACHE_DIR}/data/tmp"
touch "${CACHE_DIR}/access.log"

if [[ -n "$GITHUB_ACTIONS" ]]; then
  # Avoid permission error on older nginx
  sudo mkdir -p /var/lib/nginx/fastcgi
  sudo mkdir -p /var/lib/nginx/uwsgi
  sudo mkdir -p /var/lib/nginx/scgi
fi

echo "Start bazel cache overlay"
(
  cd "${CACHE_DIR}/" || exit 1
  nginx -p "${CACHE_DIR}" -c "${NGINX_CONF}"
) &
sleep 1

# In GitHub actions, we configure Bazel using ~/.bazelisk.
if [[ -n "$GITHUB_ACTIONS" ]]; then
    echo "BAZEL_CACHE_OVERLAY=${CACHE_DIR}" >> "${GITHUB_ENV:-/dev/null}"
    echo "build --remote_cache=http://127.0.0.1:8388/opentitan-bazel-cache" >> ~/.bazelrc
    echo "build --remote_upload_local_results=true" >> ~/.bazelrc
fi
