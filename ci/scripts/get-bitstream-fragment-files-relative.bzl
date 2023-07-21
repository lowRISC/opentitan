# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def format(target):
    provider_name = "//rules:bitstreams.bzl%BitstreamManifestFragmentInfo"
    manifest_dir = providers(target)[provider_name].fragment.dirname
    file_list = target.files.to_list()
    rel_paths = [x.path.removeprefix(manifest_dir + "/") for x in file_list]
    return "\n".join(rel_paths)
