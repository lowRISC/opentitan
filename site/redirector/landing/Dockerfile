# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM nginx

RUN rm /etc/nginx/conf.d/default.conf
COPY redirector.conf /etc/nginx/conf.d/
