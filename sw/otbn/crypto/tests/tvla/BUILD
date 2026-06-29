# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_library", "otbn_sim_test", "otbn_tvla_sim_test")

package(default_visibility = ["//visibility:public"])

# In order to reduce TVLA time, we manually adapt the scalar multiply loop to shorten the time it takes to run sign
genrule(
    name = "p256_base_short_s",
    srcs = ["//sw/otbn/crypto:p256_base.s"],
    outs = ["p256_base_short.s"],
    cmd = "sed -E 's/^([[:space:]]*).*\\/\\*[[:space:]]*SCA_TEST_REPLACE:[[:space:]]*(.*)[[:space:]]*\\*\\//\\1\\2/' $< > $@",
    tags = ["manual"],
)

otbn_library(
    name = "p256_base_short",
    srcs = [
        ":p256_base_short_s",
        "//sw/otbn/crypto:p256_b2a.s",
    ],
    tags = ["manual"],
)

otbn_sim_test(
    name = "run_p256_short",
    srcs = ["//sw/otbn/crypto:run_p256.s"],
    tags = ["manual"],
    deps = [
        ":p256_base_short",
        "//sw/otbn/crypto:p256_isoncurve",
        "//sw/otbn/crypto:p256_isoncurve_check",
        "//sw/otbn/crypto:p256_isoncurve_proj",
        "//sw/otbn/crypto:p256_shared_key",
        "//sw/otbn/crypto:p256_sign",
        "//sw/otbn/crypto:p256_verify",
    ],
)

otbn_tvla_sim_test(
    name = "p256_ecdh_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x1AD",
        "x": "const:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "const:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
    num_experiments = 5000,
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_p256_short",
    tvla_secrets = {
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    },
)

# Run a fixed versus random key with message and nonce fixed
otbn_tvla_sim_test(
    name = "p256_ecdsa_sign_tvla_test",
    timeout = "eternal",
    # Fixed secrets: value stays the same, but allow for masking (unless const)
    fixed_background_secrets = {
        "mode": "const:4:0x563",
        "msg": "const:32:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00",
    },
    num_experiments = 5000,
    # Random secrets: value is new every run and shares are re-masked
    random_background_secrets = {
        "k0_io,k1_io": "scalar_blind:64:0:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    },
    # We do not have noise, so a high threshold is just to filter false positives
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_p256_short",
    # TVLA targets: toggle between fixed and random
    # Format: "sym0,sym1": "mode:size_in_bytes:secret_hex:modulus_hex(optional)"
    tvla_secrets = {
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    },
)

genrule(
    name = "p384_internal_mult_short_s",
    srcs = ["//sw/otbn/crypto:p384_internal_mult.s"],
    outs = ["p384_internal_mult_short.s"],
    cmd = "sed -E 's/^([[:space:]]*).*\\/\\*[[:space:]]*SCA_TEST_REPLACE:[[:space:]]*(.*)[[:space:]]*\\*\\//\\1\\2/' $< > $@",
    tags = ["manual"],
)

otbn_library(
    name = "p384_internal_mult_short",
    srcs = [
        ":p384_internal_mult_short_s",
    ],
    tags = ["manual"],
)

genrule(
    name = "25519_short_s",
    srcs = ["//sw/otbn/crypto:25519.s"],
    outs = ["25519_short.s"],
    cmd = "sed -E 's/^([[:space:]]*).*\\/\\*[[:space:]]*SCA_TEST_REPLACE:[[:space:]]*(.*)[[:space:]]*\\*\\//\\1\\2/' $< > $@",
    tags = ["manual"],
)

otbn_library(
    name = "25519_short",
    srcs = [
        ":25519_short_s",
    ],
    tags = ["manual"],
)

genrule(
    name = "modexp_short_s",
    srcs = ["//sw/otbn/crypto:modexp.s"],
    outs = ["modexp_short.s"],
    cmd = "sed -E 's/^([[:space:]]*).*\\/\\*[[:space:]]*SCA_TEST_REPLACE:[[:space:]]*(.*)[[:space:]]*\\*\\//\\1\\2/' $< > $@",
    tags = ["manual"],
)

otbn_sim_test(
    name = "run_p384_short",
    srcs = ["//sw/otbn/crypto:run_p384.s"],
    tags = ["manual"],
    deps = [
        ":p384_internal_mult_short",
        "//sw/otbn/crypto:p384_a2b",
        "//sw/otbn/crypto:p384_b2a",
        "//sw/otbn/crypto:p384_base",
        "//sw/otbn/crypto:p384_base_mult",
        "//sw/otbn/crypto:p384_isoncurve",
        "//sw/otbn/crypto:p384_isoncurve_proj",
        "//sw/otbn/crypto:p384_keygen",
        "//sw/otbn/crypto:p384_keygen_from_seed",
        "//sw/otbn/crypto:p384_mem",
        "//sw/otbn/crypto:p384_modinv",
        "//sw/otbn/crypto:p384_scalar_mult",
        "//sw/otbn/crypto:p384_sign",
        "//sw/otbn/crypto:p384_verify",
    ],
)

otbn_tvla_sim_test(
    name = "p384_ecdh_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x578",
        "x": "const:64:0x00000000000000000000000000000000ca230836b439d7011a9ea916cf60d89e394d8b7047e806616c30f2d8ee0e2beb5869de54b1cac6097b8294604877f3d1",
        "y": "const:64:0x00000000000000000000000000000000aaafcad203afe2c268eef2d1d65e905d82b63bf3928c3e92cea028a9ec18818cc7e55880bf3aff6ec31ef079c181f90f",
    },
    num_experiments = 5000,
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_p384_short",
    tvla_secrets = {
        "d0_io,d1_io": "additive:64:0x32f9e2b08677a5f2adb9ce1be14cd8df800a4c9416f5c1ee1e9d19e796d2f9e05b7d3b0f4de8344e6e0012819a0c1b763eb17c275c832a51:0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    },
)

otbn_tvla_sim_test(
    name = "p384_ecdsa_sign_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x655",
        "msg": "const:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00",
    },
    num_experiments = 5000,
    random_background_secrets = {
        "k0_io,k1_io": "scalar_blind:64:0:0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    },
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_p384_short",
    tvla_secrets = {
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    },
)

otbn_sim_test(
    name = "run_curve25519_short",
    srcs = ["//sw/otbn/crypto:run_curve25519.s"],
    tags = ["manual"],
    deps = [
        ":25519_short",
        "//sw/otbn/crypto:25519_scalar",
        "//sw/otbn/crypto:field25519",
        "//sw/otbn/crypto:p256_a2b",
        "//sw/otbn/crypto:p256_b2a",
    ],
)

otbn_tvla_sim_test(
    name = "curve25519_ecdh_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x695",
        "x25519_public_key": "const:32:0x4c1cabd0a603a9103b35b326ec2466727c5fb124a4c19435db3030586768dbe6",
    },
    num_experiments = 5000,
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_curve25519_short",
    tvla_secrets = {
        "ed25519_s0,ed25519_s1": "additive:32:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0x10000000000000000000000000000000000000000000000000000000000000000",
    },
)

otbn_tvla_sim_test(
    name = "ed25519_sign_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x669",
    },
    num_experiments = 5000,
    random_background_secrets = {
        "ed25519_r0,ed25519_r1": "subtractive:96:0:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
    },
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_curve25519_short",
    tvla_secrets = {
        "ed25519_s0,ed25519_s1": "subtractive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
    },
)

otbn_sim_test(
    name = "run_rsa_short",
    srcs = [
        ":modexp_short_s",
        "//sw/otbn/crypto:div.s",
        "//sw/otbn/crypto:gcd.s",
        "//sw/otbn/crypto:montmul.s",
        "//sw/otbn/crypto:mul.s",
        "//sw/otbn/crypto:rsa_keygen.s",
        "//sw/otbn/crypto:rsa_modinv_f4.s",
        "//sw/otbn/crypto:rsa_primality.s",
        "//sw/otbn/crypto:run_rsa.s",
        "//sw/otbn/crypto:run_rsa_mem.s",
    ],
    tags = ["manual"],
)

otbn_tvla_sim_test(
    name = "rsa_2048_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x582",
        "rsa_n": "const:256:0xb5ed720fe7e1b4a65494e8e9421df94910811d23854cb07b08a34508b682b188b16fa70e4804b4c4f54a54ae2a10848abc9253ac7c6085e5b9abcbcd48515db1626b01df4e7f5f1c85b9ce1b4c8d0f77f3854c8bc4f350ad4d993a6815d0d62ac83b47a257adb40023e1acf003d27953f19c5cbede1af58e42ef12ad9907c20ca428f8b7dbb6f3434936b1108d17ee343d7127f8885ff2513eb834c17bf1c4ddec0d61cc26f5f683c10c0e48676608811e9341f2898f690bc9fafd3b7e46d375e2178a141faf0d637767da550de4c5b9939af133ceba7cd2734df4ad269c166180afd8c35060de8ac302ca911aa3f92d139ed1595523a7f6c201cfafed4c17b5",
        "inout": "const:256:0x95fb986cd4aeee4b013effc1d183670380a9e2133ecc6a38dbbfff3f8ef20e1923a5e3741eac8772ee80f28994968fcabd6d454b7791263872bc68d97b6f4fbb76cee24f205d812ad36f2fcb6c11145943009a051c39c18c45b53ee19e51df0254b31eb991783718fb35c51dec249956bceb0276eaee88d8ecdeae2c08ac62a0018408af3923206e911a7ecf6ad786255fa69d63d333e6f44ebd3f5e6ebb7c82443c694d913e200492c89f046943f2dc7d8cf9951c6a33fa721558d1956fb552349ded082714be6a8bff775fd05162744d229fc9fac72509476bdc6434e5187bf3a1cc426cc13f0a10dcf0d15f28abcecfe5674782f232464b1a890d42b6fdd0",
    },
    num_experiments = 5000,
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_rsa_short",
    tvla_secrets = {
        "rsa_d0,rsa_d1": "boolean:256:0x51a84a52295a7da34ac3abe746edfd3e7651fdaa3be2b8340124878fe99bafe4130072934e700e537965ebac60e51918cc9b4143627050a95435703cac011974cd200aaf18a4c3242241cbe924eb0bce6357a98bf2d2e39b660128de1f2ca5747e7b5d23d906f68c398ec9f8d13e5f86f623a0dd6b03dec403f71b03207502fbb6c7d812f391e010cbed264655d11ab63c262a803196a128df72ecf1c65ed7f742371e4c4ee355f44cfae81ec0a256da9aa3eb1935fc509d366de08c7edb522411670cd7ee0053bb9395ac4cbe0af6f3cdd1c24e225ee47aa4f381764cfab389db993fed537f397fbff31362a85872993bc467dde42b66894f4cb3ce712b2ee1",
    },
)

otbn_tvla_sim_test(
    name = "rsa_512_tvla_test",
    timeout = "eternal",
    fixed_background_secrets = {
        "mode": "const:4:0x3ad",
        "rsa_n": "const:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "inout": "const:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
    num_experiments = 1800,
    t_threshold = "7.0",
    tags = ["manual"],
    target = ":run_rsa_short",
    tvla_secrets = {
        "rsa_d0,rsa_d1": "boolean:64:0x322c127f274460106c92fed934f1c6d695dfc595227fd7a607c032cec45983351d0b0bc8f3dff3b6c9ad7832dd18d46d82a6173a921aaf8adaa5b31fa0d07f7d",
    },
)
