# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

exclude -inst $::env(DUT_TOP) -toggle 'tl_i.a_user.rsvd'
exclude -inst $::env(DUT_TOP) -toggle 'tl_i.a_param'
exclude -inst $::env(DUT_TOP) -toggle 'tl_o.d_param'
exclude -inst $::env(DUT_TOP) -toggle 'tl_o.d_sink'
