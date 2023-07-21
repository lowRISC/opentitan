# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def format(target):
    provider_name = "//rules:bitstreams.bzl%BitstreamManifestFragmentInfo"
    return providers(target)[provider_name].fragment.dirname
