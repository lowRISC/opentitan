# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

nist_cavp = module_extension(
    implementation = lambda _: _nist_cavp_repos(),
)

def _nist_cavp_repos():
    """Load NIST CAVP test vectors

    The NIST website that serves the test vectors (csrc.nist.gov) is sometimes
    unreliable. To improve availability, the NIST test vectors are hosted in a
    lowRISC GCS storage bucket (ot-crypto-test-vectors). To add new test
    vectors, upload the zip file to the GCS bucket, update the manifest there
    to indicate the original download URL, and use the public link to fetch the
    archive instead of the NIST website.
    """
    http_archive(
        name = "nist_cavp_drbg_sp_800_90a_root",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "5f7e5658ebd5b4e6785a7b12fa32333511d2acc2f2d9c5ae1ffa16b699377769",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/drbgtestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_ecdsa_fips_186_4",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        strip_prefix = "186-4ecdsatestvectors",
        sha256 = "fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/186-4ecdsatestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/186-4ecdsatestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_sha2_fips_180_4",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        strip_prefix = "shabytetestvectors",
        sha256 = "929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/shabytetestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_sha3_fips_202",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "cd07701af2e47f5cc889d642528b4bf11f8b6eb55797c7307a96828ed8d8fc8c",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/sha-3bytetestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_shake_fips_202",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "debfebc3157b3ceea002b84ca38476420389a3bf7e97dc5f53ea4689a16de4c7",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebytetestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/shakebytetestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_aes_kat",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/KAT_AES.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/KAT_AES.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_aes_kw_sp_800_38f",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        strip_prefix = "kwtestvectors",
        sha256 = "04a4a82e4de65bca505125295003f9c75a5a815afda046dc83661b8b580dfdf3",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/kwtestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/kwtestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_aes_gcm",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/gcmtestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_ecdh_sp_800_56a",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "5fff092551f2d72e89a3d9362711878708f9a14b502f0dfae819649105b0ea39",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/components/ecccdhtestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/ecccdhtestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_rsa_fips_186_3",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "8405aeb3572a4f98ed4b1a3ccb3f2f49e725462dd28ec4759d6a15d88855d19c",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/186-3rsatestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/186-3rsatestvectors.zip",
        ],
    )
    http_archive(
        name = "nist_cavp_hmac_fips_198_1",
        build_file = Label("//third_party/nist_cavp_testvectors:BUILD.nist_cavp_common.bazel"),
        sha256 = "418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd",
        urls = [
            "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/hmactestvectors.zip",
            "https://storage.googleapis.com/ot-crypto-test-vectors/nist/hmactestvectors.zip",
        ],
    )
