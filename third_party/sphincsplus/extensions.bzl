# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:repo.bzl", "http_archive_or_local")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

sphincsplus = module_extension(
    implementation = lambda _: _sphincsplus_repos(),
)

def _sphincsplus_repos(local = None):
    http_archive(
        name = "sphincsplus_shake256_kat",
        build_file = Label("@lowrisc_opentitan//third_party/sphincsplus:BUILD.sphincsplus_common.bazel"),
        sha256 = "95f5c79995ad8a3bc752c760f93ec409763cf2b23d1a7a7404219f26d665f7ab",
        urls = [
            # Self-hosted GCP ZIP that contains the 128s/SHAKE256 test
            # vectors for the FIPS-205 Initial Public Draft (fips205-ipd),
            # which does not have an official NIST-hosted release yet.
            "https://storage.googleapis.com/ot-crypto-test-vectors/sphincsplus/sphincsplus_shake256_128s_fips205-ipd.zip",
        ],
    )
    http_archive(
        name = "sphincsplus_sha256_kat",
        build_file = Label("@lowrisc_opentitan//third_party/sphincsplus:BUILD.sphincsplus_common.bazel"),
        sha256 = "1656a6aa06d731905ef72fcfbdf65f365d4c0fe89cbf3b24d1dbb64669a25e35",
        urls = [
            # Self-hosted GCP ZIP that contains the 128s/SHAKE256 test
            # vectors for the FIPS-205 Initial Public Draft (fips205-ipd),
            # which does not have an official NIST-hosted release yet.
            "https://storage.googleapis.com/ot-crypto-test-vectors/sphincsplus/sphincsplus_sha256_128s_fips205-ipd.zip",
        ],
    )
    http_archive_or_local(
        name = "sphincsplus_fips205_ipd",
        local = local,
        url = "https://github.com/sphincs/sphincsplus/archive/129b72c80e122a22a61f71b5d2b042770890ccee.tar.gz",
        strip_prefix = "sphincsplus-129b72c80e122a22a61f71b5d2b042770890ccee/ref",
        build_file = "@lowrisc_opentitan//third_party/sphincsplus:BUILD.sphincsplus.bazel",
        sha256 = "b301faa7a42ef538323a732929d49341b1cbd8375f643f7d98ca32cd6efacc32",
        patches = [
            Label("@lowrisc_opentitan//third_party/sphincsplus/patches:sphincsplus-namespace.patch"),
        ],
        patch_args = ["-p2"],
    )
