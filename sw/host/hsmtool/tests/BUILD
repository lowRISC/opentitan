# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

sh_library(
    name = "test_lib",
    srcs = ["test_lib.sh"],
)

[
    sh_test(
        name = "slh_dsa_generate_test_{}".format(parameter_set),
        srcs = ["hsmtool_runner.sh"],
        args = [
            "--module=$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
            "--token=fake_keys -u user -p 123456",
            "slh-dsa",
            "generate",
            "--label fake",
            "--parameter-set {}".format(parameter_set),
        ],
        data = [
            "//signing/softhsm",
            "//signing/softhsm:conf",
            "//sw/host/hsmtool",
            "@softhsm2//:gen_dir",
        ],
        env = {
            "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        },
        deps = [":test_lib"],
    )
    for parameter_set in [
        "sha2-128s",
        "shake-128s",
        "sha2-128f",
        "shake-128f",
        "sha2-192s",
        "shake-192s",
        "sha2-192f",
        "shake-192f",
        "sha2-256s",
        "shake-256s",
        "sha2-256f",
        "shake-256f",
    ]
]

sh_test(
    name = "slh_dsa_roundtrip_test",
    srcs = ["hsmtool_roundtrip_runner.sh"],
    args = [
        "slh-dsa",
        "fake_app_prod_slh_dsa",
        "$(rootpath :tqbf.txt)",
    ],
    data = [
        "tqbf.txt",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/host/hsmtool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
    },
    deps = [":test_lib"],
)

sh_test(
    name = "token_exists_test",
    srcs = ["hsmtool_runner.sh"],
    args = [
        "--module=$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        "--token=fake_keys",
        "token",
        "list",
    ],
    data = [
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/host/hsmtool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
    },
    deps = [":test_lib"],
)

genrule(
    name = "tqbf_digest",
    srcs = ["tqbf.txt"],
    outs = ["tqbf.digest"],
    cmd = """
        sha256sum $< | cut -f1 -d' ' | tr '[:lower:]' '[:upper:]' | basenc -d --base16 > $@
    """,
)

# ECDSA-Sign a digest with opentitantool and then verify the signature with hsmtool.
sh_test(
    name = "ecdsa_opentitantool_sign_hsmtool_verify_test",
    srcs = ["ot_hsm_runner.sh"],
    data = [
        ":tqbf_digest",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset",
        "//sw/host/hsmtool",
        "//sw/host/opentitantool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "FIRST": "opentitantool",
        "OTTOOL_ARGS": """
            --rcfile=
            ecdsa sign
                sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.der
                --input=$(rootpath :tqbf_digest)
                --output=tqbf.ecdsa_sig
        """,
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        "HSMTOOL_ARGS": """
            -t fake_keys -u user -p 123456
            ecdsa verify
                --little-endian
                --label=fake_app_prod_ecdsa
                $(rootpath :tqbf_digest)
                tqbf.ecdsa_sig
        """,
    },
    deps = [":test_lib"],
)

# ECDSA-Sign a digest with hsmtool and then verify the signature with opentitantool.
sh_test(
    name = "ecdsa_hsmtool_sign_opentitantool_verify_test",
    srcs = ["ot_hsm_runner.sh"],
    data = [
        "tqbf.txt",
        ":tqbf_digest",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub",
        "//sw/host/hsmtool",
        "//sw/host/opentitantool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "FIRST": "hsmtool",
        "OTTOOL_ARGS": """
            --rcfile=
            ecdsa verify
                --digest-file=$(rootpath :tqbf_digest)
                --signature-file=tqbf.ecdsa_sig
                sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.pub.der
        """,
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        # This hsmtool invocation computes the digest from the plain-text `tqbf.txt` input file.
        "HSMTOOL_ARGS": """
            -t fake_keys -u user -p 123456
            ecdsa sign
                --little-endian
                --format=plain-text
                --label=fake_app_prod_ecdsa
                --output=tqbf.ecdsa_sig
                sw/host/hsmtool/tests/tqbf.txt
        """,
    },
    deps = [":test_lib"],
)

# Currently, there are two hierarchies in hsmtool implementing the same underlying algorithm:
# SPX (SPHINCS+) and SLH-DSA. SPHINCS+ is the pre-standardization form of SLH-DSA, and is
# supported for legacy reasons. We want to test that the implementations of SPHINCS+ and
# SLH-DSA are equivalent from a signing perspective. Note that historically, the legacy
# SPHINCS+ hierarchy has only accepted keys in OpenTitan's custom RAW PEM format, whereas
# the newer SLH-DSA hierarchy only accepts key in the standardized PEM/DER formats.
_SPX_HIERARCHIES = [
    "spx",
    "slh_dsa",
]

_SPX_TEST_CASES = {
    "pure": {
        "domain": "Pure",
        "format": "plain-text",
        "rev_flag": "--spx-hash-reversal-bug=false",
    },
    "prehashed": {
        "domain": "PreHashedSha256",
        "format": "sha256-hash",
        "rev_flag": "--spx-hash-reversal-bug=false",
    },
    "hashreversed": {
        "domain": "PreHashedSha256",
        "format": "sha256-hash-reversed",
        "rev_flag": "--spx-hash-reversal-bug=true",
    },
}

# SPHINCS+/SLH-DSA sign a digest with opentitantool and then verify the signature with hsmtool.
[
    sh_test(
        name = "{}_{}_opentitantool_sign_hsmtool_verify_test".format(algorithm, name),
        srcs = ["ot_hsm_runner.sh"],
        data = [
            ":tqbf_digest",
            "//signing/softhsm",
            "//signing/softhsm:conf",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:{}_keyset".format(algorithm),
            "//sw/host/hsmtool",
            "//sw/host/opentitantool",
            "@softhsm2//:gen_dir",
        ],
        env = {
            "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
            "FIRST": "opentitantool",
            "OTTOOL_ARGS": """
                --rcfile=
                spx sign {rev_flag}
                    --domain={domain}
                    $(rootpath :tqbf_digest)
                    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_{algorithm}.pem
                    --output=tqbf.{algorithm}_sig
            """.format(
                algorithm = algorithm,
                domain = param["domain"],
                rev_flag = param["rev_flag"],
            ),
            "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
            "HSMTOOL_ARGS": """
                -t fake_keys -u user -p 123456
                {cmd} verify
                    --label=fake_app_prod_{algorithm}
                    --domain={domain}
                    --format={fmt}
                    $(rootpath :tqbf_digest)
                    tqbf.{algorithm}_sig
            """.format(
                algorithm = algorithm,
                cmd = algorithm.replace("_", "-"),
                domain = param["domain"],
                fmt = param["format"],
            ),
        } | ({"HSMTOOL_SPX_MODULE": "pkcs11-ef"} if algorithm == "spx" else {}),
        deps = [":test_lib"],
    )
    for algorithm in _SPX_HIERARCHIES
    for name, param in _SPX_TEST_CASES.items()
]

# SPHINCS+/SLH-DSA sign a digest with hsmtool and then verify the signature with opentitantool.
[
    sh_test(
        name = "{}_{}_hsmtool_sign_opentitantool_verify_test".format(algorithm, name),
        srcs = ["ot_hsm_runner.sh"],
        data = [
            ":tqbf_digest",
            "//signing/softhsm",
            "//signing/softhsm:conf",
            "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_{}_pub".format(algorithm),
            "//sw/host/hsmtool",
            "//sw/host/opentitantool",
            "@softhsm2//:gen_dir",
        ],
        env = {
            "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
            "FIRST": "hsmtool",
            "OTTOOL_ARGS": """
                --rcfile=
                spx verify {rev_flag}
                    --domain={domain}
                    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_{algorithm}.pub.pem
                    $(rootpath :tqbf_digest)
                    tqbf.{algorithm}_sig
            """.format(
                algorithm = algorithm,
                domain = param["domain"],
                rev_flag = param["rev_flag"],
            ),
            "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
            "HSMTOOL_ARGS": """
                -t fake_keys -u user -p 123456
                {cmd} sign
                    --label=fake_app_prod_{algorithm}
                    --domain={domain}
                    --format={fmt}
                    --output=tqbf.{algorithm}_sig
                    $(rootpath :tqbf_digest)
            """.format(
                algorithm = algorithm,
                cmd = algorithm.replace("_", "-"),
                domain = param["domain"],
                fmt = param["format"],
            ),
        } | ({"HSMTOOL_SPX_MODULE": "pkcs11-ef"} if algorithm == "spx" else {}),
        deps = [":test_lib"],
    )
    for algorithm in _SPX_HIERARCHIES
    for name, param in _SPX_TEST_CASES.items()
]

filegroup(
    name = "image_bin",
    # A hand assembled binary image.
    # dd if=/dev/zero of=image.bin bs=1k count=1
    # Then, use hexdump tools (e.g. `xxd` and `xxd -r`) to insert the following bytes:
    #
    # 00000330: 0000 0000 4f54 5245 476c 0200 0004 0000  ................
    # 00000340: 0004 0000 0000 0000 0000 0000 0000 0000  ................
    #
    # This sets the identifier, manifest_version, signed_region_end and length fields.
    srcs = ["image.bin"],
)

genrule(
    name = "image_digest",
    srcs = [":image_bin"],
    outs = ["image.digest"],
    # Opentitantool computes the digest by excluding the signature region of the manifest.
    # The signature region is the first 384 bytes.
    cmd = """
        dd if=$< bs=1 skip=384 | sha256sum - | cut -f1 -d' ' | tr '[:lower:]' '[:upper:]' | basenc -d --base16 > $@
    """,
)

# Verify the opentitantool image digest calculation.
sh_test(
    name = "image_digest_test",
    srcs = ["image_digest_test.sh"],
    data = [
        ":image_bin",
        ":image_digest",
        "//sw/host/opentitantool",
    ],
    env = {
        "IMAGE_BIN": "$(rootpath :image_bin)",
        "KNOWN_DIGEST": "$(rootpath :image_digest)",
    },
    deps = [":test_lib"],
)

# ECDSA-Sign an image with opentitantool and then verify the signature with hsmtool.
sh_test(
    name = "manifest_opentitantool_sign_hsmtool_verify_test",
    srcs = ["ot_hsm_runner.sh"],
    data = [
        ":image_bin",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:ecdsa_keyset",
        "//sw/host/hsmtool",
        "//sw/host/opentitantool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "FIRST": "opentitantool",
        "OTTOOL_ARGS": """
            --rcfile=
            image manifest update
                --ecdsa-key=sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.der
                --output=image.signed_bin
                $(rootpath :image_bin)
        """,
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        "HSMTOOL_ARGS": """
            -t fake_keys -u user -p 123456
            ecdsa verify
                --little-endian
                --label=fake_app_prod_ecdsa
                --format=slice:384..1024
                --signature-at=0..64
                image.signed_bin
        """,
    },
    deps = [":test_lib"],
)

# ECDSA-Sign an image with hsmtool and then verify the signature with opentitantool.
sh_test(
    name = "manifest_hsmtool_sign_opentitantool_verify_test",
    srcs = ["ot_hsm_runner.sh"],
    data = [
        ":image_bin",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa_pub",
        "//sw/host/hsmtool",
        "//sw/host/opentitantool",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "FIRST": "hsmtool",
        "PREPARE_CMD": """
            sw/host/opentitantool/opentitantool image manifest update
                --ecdsa-key=sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.pub.der
                --output=image.signed_bin
                $(rootpath :image_bin)
        """,
        "OTTOOL_ARGS": """
            --rcfile=
            image manifest verify
                image.signed_bin
        """,
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
        "HSMTOOL_ARGS": """
            -t fake_keys -u user -p 123456
            ecdsa sign
                --little-endian
                --label=fake_app_prod_ecdsa
                --format=slice:384..1024
                --update-in-place=0..64
                image.signed_bin
        """,
    },
    deps = [":test_lib"],
)

# SLH-DSA PEM-format PKCS#8/SPKI encoded keys with RFC 9909 HashSLH-DSA OIDs.
filegroup(
    name = "hash_slh_dsa_keys",
    testonly = True,
    srcs = [
        "hash-slh-dsa-{}-{}.pem".format(parameter_set, key_type)
        for key_type in [
            "public",
            "private",
        ]
        for parameter_set in [
            "sha2-128s",
            "shake-128s",
        ]
    ],
)

# Verify that hsmtool can accept SLH-DSA keys with RFC9909 HashSLH-DSA
# OIDs, since some exported PKCS#8/SPKI encoded keys might contain
# algorithm OIDs describing key usage with HashSLH-DSA.
sh_test(
    name = "hsmtool_hash_slh_dsa_key_test",
    srcs = ["hash_slh_dsa_key_test.sh"],
    args = ["$(locations :hash_slh_dsa_keys)"],
    data = [
        ":hash_slh_dsa_keys",
        "//signing/softhsm",
        "//signing/softhsm:conf",
        "//sw/host/hsmtool",
        "@openssl",
        "@softhsm2//:gen_dir",
    ],
    env = {
        "OPENSSL": "$(rootpath @openssl)",
        "SOFTHSM2_CONF": "$(rootpath //signing/softhsm:conf)",
        "HSMTOOL_MODULE": "$(rootpath @softhsm2//:gen_dir)/lib/softhsm/libsofthsm2.so",
    },
    # hsmtool currently does not recognize the HashSLH-DSA algorithm identifiers
    # (OIDs) in the PKCS#8/SPKI ASN.1 encodings, despite the fact that it supports
    # use of the underlying `CKM_HASH_SLH_DSA` mechanism type.
    tags = ["broken"],
    deps = [":test_lib"],
)
