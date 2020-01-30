# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Functions to convert validated top-level and peripheral module HJSON
to SVD files."""

from .lib import convert_top_to_svd, write_svd
