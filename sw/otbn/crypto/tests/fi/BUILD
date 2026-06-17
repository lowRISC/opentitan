# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_fi_sim_test")

package(default_visibility = ["//visibility:public"])

# Look for collisions in 'r' with different nonces
otbn_fi_sim_test(
    name = "p256_ecdsa_sign_fi_nonce_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 32,
    collision_symbol = "r",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p256",
    target_a_secrets = {
        "mode": "unmasked:4:0x563",
        "msg": "unmasked:32:0x06d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        "k0_io,k1_io": "scalar_blind:64:0x1111111111111111111111111111111111111111111111111111111111111111:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x563",
        "msg": "unmasked:32:0x06d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        "k0_io,k1_io": "scalar_blind:64:0x9999999999999999999999999999999999999999999999999999999999999999:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    },
)

# Look for collisions of the output x_r between two separate messages while needing the ok status
otbn_fi_sim_test(
    name = "p256_ecdsa_verify_msg_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",  # We call a collision of r if they match 75%
    collision_size = 32,  # x_r is a 256-bit word
    collision_symbol = "x_r",
    fixed_instruction_count = False,  # Verify is a variable time algorithm
    ok_size = 4,  # ok is a 32-bit word
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p256",
    # Correct signature
    target_a_secrets = {
        "mode": "unmasked:4:0x5D8",
        "msg": "unmasked:32:0x06d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",
        "r": "unmasked:32:0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a",
        "s": "unmasked:32:0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605",
        "x": "unmasked:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "unmasked:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x5D8",
        "msg": "unmasked:32:0x16d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",  # Changed byte
        "r": "unmasked:32:0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a",
        "s": "unmasked:32:0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605",
        "x": "unmasked:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "unmasked:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
)

# Look for collisions of the output x_r between two separate public keys while needing the ok status
otbn_fi_sim_test(
    name = "p256_ecdsa_verify_pubkey_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 32,
    collision_symbol = "x_r",
    fixed_instruction_count = False,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p256",
    # Correct signature and public key
    target_a_secrets = {
        "mode": "unmasked:4:0x5D8",
        "msg": "unmasked:32:0x06d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",
        "r": "unmasked:32:0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a",
        "s": "unmasked:32:0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605",
        "x": "unmasked:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "unmasked:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
    # Same msg, r, s, but different public key
    target_b_secrets = {
        "mode": "unmasked:4:0x5D8",
        "msg": "unmasked:32:0x06d712076ce90fefb028ad8a90d4d90b17d015f1b54d7452400bdd7d4456fd21",
        "r": "unmasked:32:0x815215ad7dd27f336b35843cbe064de299504edd0c7d87dd1147ea5680a9674a",
        "s": "unmasked:32:0xa3991e01c444042086e30cd999e589ad4dad9404e90a6d17d0b1051ec93fd605",
        "x": "unmasked:32:0x2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838",
        "y": "unmasked:32:0xc7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
    },
)

# Look for collisions of the shared secret between two different secret keys
otbn_fi_sim_test(
    name = "p256_ecdh_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_mode = "boolean",
    collision_size = 32,
    collision_symbol = "x,y",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p256",
    # Secret A
    target_a_secrets = {
        "mode": "unmasked:4:0x1AD",
        "d0_io,d1_io": "additive:64:0x1420fc41742102631b76ebe83fdfa3799590ef5db0b2c78121d0a016fe6d1071:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        "x": "unmasked:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "unmasked:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
    # Secret B (different private key, same public key)
    target_b_secrets = {
        "mode": "unmasked:4:0x1AD",
        "d0_io,d1_io": "additive:64:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        "x": "unmasked:32:0xb5511a6afacdc5461628ce58db6c8bf36ec0c0b2f36b06899773b7b3bfa8c334",
        "y": "unmasked:32:0x42a1c6971f31c14343dd09eab53a17fa7f7a11d0ab9c6924a87070589e008c2e",
    },
)

# Look for collisions in 'r' with different nonces for P384
otbn_fi_sim_test(
    name = "p384_ecdsa_sign_fi_nonce_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 48,  # P384 r is 48 bytes
    collision_symbol = "r",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x0",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p384",
    target_a_secrets = {
        "mode": "unmasked:4:0x655",
        "msg": "unmasked:64:0x00000000000000000000000000000000555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555",
        "d0_io,d1_io": "additive:64:0x32f9e2b08677a5f2adb9ce1be14cd8df800a4c9416f5c1ee1e9d19e796d2f9e05b7d3b0f4de8344e6e0012819a0c1b763eb17c275c832a51:0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        "k0_io,k1_io": "scalar_blind:64:0x111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111:0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x655",
        "msg": "unmasked:64:0x00000000000000000000000000000000555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555",
        "d0_io,d1_io": "additive:64:0x32f9e2b08677a5f2adb9ce1be14cd8df800a4c9416f5c1ee1e9d19e796d2f9e05b7d3b0f4de8344e6e0012819a0c1b763eb17c275c832a51:0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        "k0_io,k1_io": "scalar_blind:64:0x999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999:0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    },
)

# Look for collisions of the output x_r between two separate public keys while needing the ok status
otbn_fi_sim_test(
    name = "p384_ecdsa_verify_pubkey_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 48,
    collision_symbol = "x_r",
    fixed_instruction_count = False,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_p384",
    # Correct signature and public key A
    target_a_secrets = {
        "mode": "unmasked:4:0x0BD",
        "msg": "unmasked:64:0x00000000000000000000000000000000555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555",
        "r": "unmasked:64:0x00000000000000000000000000000000b2fcf95c7c0d8125b45990dbd3c4305349d29eef0235d77ec16c09de12d35b3856e186cf9a1a30fc2b23ce3ab68c28d8",
        "s": "unmasked:64:0x000000000000000000000000000000001a72ebdde34d88c1fa9554e0f19a653d80eb391d3e7f68950016f9c3a78101eb77e415a198144c27752042f524bc1bf9",
        "x": "unmasked:64:0x00000000000000000000000000000000ca230836b439d7011a9ea916cf60d89e394d8b7047e806616c30f2d8ee0e2beb5869de54b1cac6097b8294604877f3d1",
        "y": "unmasked:64:0x00000000000000000000000000000000aaafcad203afe2c268eef2d1d65e905d82b63bf3928c3e92cea028a9ec18818cc7e55880bf3aff6ec31ef079c181f90f",
    },
    # Same msg, r, s, but public key B (base point G)
    target_b_secrets = {
        "mode": "unmasked:4:0x0BD",
        "msg": "unmasked:64:0x00000000000000000000000000000000555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555",
        "r": "unmasked:64:0x00000000000000000000000000000000b2fcf95c7c0d8125b45990dbd3c4305349d29eef0235d77ec16c09de12d35b3856e186cf9a1a30fc2b23ce3ab68c28d8",
        "s": "unmasked:64:0x000000000000000000000000000000001a72ebdde34d88c1fa9554e0f19a653d80eb391d3e7f68950016f9c3a78101eb77e415a198144c27752042f524bc1bf9",
        "x": "unmasked:64:0x00000000000000000000000000000000aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "y": "unmasked:64:0x000000000000000000000000000000003617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
    },
)

# Look for collisions of the shared secret between two different public keys
otbn_fi_sim_test(
    name = "curve25519_ecdh_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_mode = "boolean",
    collision_size = 64,
    collision_symbol = "x25519_shared_key",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "x25519_ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_curve25519",
    # Secret A
    target_a_secrets = {
        "mode": "unmasked:4:0x695",
        "ed25519_s0,ed25519_s1": "additive:32:0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0x10000000000000000000000000000000000000000000000000000000000000000",
        "x25519_public_key": "unmasked:32:0x4c1cabd0a603a9103b35b326ec2466727c5fb124a4c19435db3030586768dbe6",
    },
    # Secret B (different private key, same public key)
    target_b_secrets = {
        "mode": "unmasked:4:0x695",
        "ed25519_s0,ed25519_s1": "additive:32:0x012233445566778899aabbccddeeff00112233445566778899aabbccdd1eff00:0x10000000000000000000000000000000000000000000000000000000000000000",
        "x25519_public_key": "unmasked:32:0x4c1cabd0a603a9103b35b326ec2466727c5fb124a4c19435db3030586768dbe6",
    },
)

# # Look for collisions in RSA 512 decryption
otbn_fi_sim_test(
    name = "rsa_512_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 64,
    collision_symbol = "inout",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_rsa",
    target_a_secrets = {
        "mode": "unmasked:4:0x3ad",  # MODE_RSA_512_MODEXP
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "rsa_d0": "unmasked:64:0x354d9c10865d447ebaac7fe326a9d65724726953c74d2e9098051a5b9148bcfed742487a13f0350dbb897a967fb872e83acd05430c8ba533fe8b2e91e902ef79",
        "rsa_d1": "unmasked:64:0x07618e6fa119246ed63e813a12581081b1adacc6e532f9369fc5289555113fcbca4943b2e02fc6bb722402a4a2a0a685b86b12799e910ab9242e9d8e49d29004",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
    # Different ciphertext
    target_b_secrets = {
        "mode": "unmasked:4:0x3ad",
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "rsa_d0": "unmasked:64:0x354d9c10865d447ebaac7fe326a9d65724726953c74d2e9098051a5b9148bcfed742487a13f0350dbb897a967fb872e83acd05430c8ba533fe8b2e91e902ef79",
        "rsa_d1": "unmasked:64:0x07618e6fa119246ed63e813a12581081b1adacc6e532f9369fc5289555113fcbca4943b2e02fc6bb722402a4a2a0a685b86b12799e910ab9242e9d8e49d29004",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216b",
    },
)

# Look for collisions in RSA 512 decryption between two different exponents
otbn_fi_sim_test(
    name = "rsa_512_fi_exp_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 64,
    collision_symbol = "inout",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_rsa",
    target_a_secrets = {
        "mode": "unmasked:4:0x3ad",  # MODE_RSA_512_MODEXP
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "rsa_d0": "unmasked:64:0x354d9c10865d447ebaac7fe326a9d65724726953c74d2e9098051a5b9148bcfed742487a13f0350dbb897a967fb872e83acd05430c8ba533fe8b2e91e902ef79",
        "rsa_d1": "unmasked:64:0x07618e6fa119246ed63e813a12581081b1adacc6e532f9369fc5289555113fcbca4943b2e02fc6bb722402a4a2a0a685b86b12799e910ab9242e9d8e49d29004",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
    # Same ciphertext, different exponent share (d0 modified)
    target_b_secrets = {
        "mode": "unmasked:4:0x3ad",
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "rsa_d0": "unmasked:64:0x354d9c10865d447ebaac7fe326a9d65724726953c74d2e9098051a5b9148bcfed742487a13f0350dbb897a967fb872e83acd05430c8ba533fe8b2e91e902ef78",
        "rsa_d1": "unmasked:64:0x07618e6fa119246ed63e813a12581081b1adacc6e532f9369fc5289555113fcbca4943b2e02fc6bb722402a4a2a0a685b86b12799e910ab9242e9d8e49d29004",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
)

# Look for collisions in RSA 512 verification (different signatures)
otbn_fi_sim_test(
    name = "rsa_512_verify_fi_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 64,
    collision_symbol = "inout",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_rsa",
    target_a_secrets = {
        "mode": "unmasked:4:0x37f",  # MODE_RSA_512_MODEXP_F4
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
    # Different signature
    target_b_secrets = {
        "mode": "unmasked:4:0x37f",
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216b",
    },
)

# Look for collisions in RSA 512 verification between two different public keys
otbn_fi_sim_test(
    name = "rsa_512_verify_fi_pubkey_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 64,
    collision_symbol = "inout",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "ok",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_rsa",
    target_a_secrets = {
        "mode": "unmasked:4:0x37f",  # MODE_RSA_512_MODEXP_F4
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec21",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
    # Same signature, different public modulus (rsa_n modified)
    target_b_secrets = {
        "mode": "unmasked:4:0x37f",
        "rsa_n": "unmasked:64:0x906ce5d361397c1ce1f5b75760a23b20786e52ca82f66ec7216e982b5945a19afe4aba4e1c59d1aa020b035ef4c08da0658e9702c9bb46392d3b81ce594dec22",
        "inout": "unmasked:64:0xd487ce1eaf19922ad9b8a714e61a441c12e0c8b2bad640fb19488dec4f65d4d9259f4329e6f4590b9a164106cf6a659eb4862b21fb97d43588561712e8e5216a",
    },
)

# Look for collisions in 'R' with different nonces for Ed25519
otbn_fi_sim_test(
    name = "ed25519_sign_fi_nonce_test",
    timeout = "eternal",
    attack_mode = "collision",
    col_threshold = "0.75",
    collision_size = 32,
    collision_symbol = "ed25519_sig_R",
    fixed_instruction_count = True,
    ok_size = 4,
    ok_symbol = "x25519_ok",
    ok_value = "0x0",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_curve25519",
    target_a_secrets = {
        "mode": "unmasked:4:0x669",
        "ed25519_s0,ed25519_s1": "additive:64:0x512233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
        "ed25519_r0,ed25519_r1": "additive:96:0x1111111111111111111111111111111111111111111111111111111111111111:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x669",
        "ed25519_s0,ed25519_s1": "additive:64:0x512233445566778899aabbccddeeff00112233445566778899aabbccddeeff00:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
        "ed25519_r0,ed25519_r1": "additive:96:0x2222222222222222222222222222222222222222222222222222222222222222:0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed",
    },
)

# Ed25519 Verification FI test (message collision)
otbn_fi_sim_test(
    name = "ed25519_verify_fi_msg_collision_test",
    timeout = "eternal",
    attack_mode = "collision",
    collision_size = 32,
    collision_symbol = "ed25519_verify_rhs",
    fixed_instruction_count = False,
    ok_size = 4,
    ok_symbol = "ed25519_verify_result",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_curve25519",
    target_a_secrets = {
        "mode": "unmasked:4:0x54E",
        "ed25519_hash_k": "unmasked:64:0x9f0e3ca07bee6837283462046ae8b109acf2337c37117420c7228a98dc5bf10ec2a4a7bc4df02282f0f34d280df15d037b82c32003dabdffe76f536b2b067127",
        "ed25519_sig_R": "unmasked:32:0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5",
        "ed25519_sig_S": "unmasked:32:0x0b107a8e4341516524be5b59f0f55bd26bb4f91c70391ec6ac3ba3901582b85f",
        "ed25519_public_key": "unmasked:32:0x1a5107f7681a02af2523a6daf372e10e3a0764c9d3fe4bd5b70ab18201985ad7",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x54E",
        "ed25519_hash_k": "unmasked:64:0x9f0e3ca07bee6837283462046ae8b109acf2337c37117420c7228a98dc5bf10ec2a4a7bc4df02282f0f34d280df15d037b82c32003dabdffe76f536b2b067128",
        "ed25519_sig_R": "unmasked:32:0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5",
        "ed25519_sig_S": "unmasked:32:0x0b107a8e4341516524be5b59f0f55bd26bb4f91c70391ec6ac3ba3901582b85f",
        "ed25519_public_key": "unmasked:32:0x1a5107f7681a02af2523a6daf372e10e3a0764c9d3fe4bd5b70ab18201985ad7",
    },
)

# Ed25519 Verification FI test (public key collision)
otbn_fi_sim_test(
    name = "ed25519_verify_fi_pubkey_collision_test",
    timeout = "eternal",
    attack_mode = "collision",
    collision_size = 32,
    collision_symbol = "ed25519_verify_rhs",
    fixed_instruction_count = False,
    ok_size = 4,
    ok_symbol = "ed25519_verify_result",
    ok_value = "0x739",
    tags = ["manual"],
    target = "//sw/otbn/crypto:run_curve25519",
    target_a_secrets = {
        "mode": "unmasked:4:0x54E",
        "ed25519_hash_k": "unmasked:64:0x9f0e3ca07bee6837283462046ae8b109acf2337c37117420c7228a98dc5bf10ec2a4a7bc4df02282f0f34d280df15d037b82c32003dabdffe76f536b2b067127",
        "ed25519_sig_R": "unmasked:32:0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5",
        "ed25519_sig_S": "unmasked:32:0x0b107a8e4341516524be5b59f0f55bd26bb4f91c70391ec6ac3ba3901582b85f",
        "ed25519_public_key": "unmasked:32:0x1a5107f7681a02af2523a6daf372e10e3a0764c9d3fe4bd5b70ab18201985ad7",
    },
    target_b_secrets = {
        "mode": "unmasked:4:0x54E",
        "ed25519_hash_k": "unmasked:64:0x9f0e3ca07bee6837283462046ae8b109acf2337c37117420c7228a98dc5bf10ec2a4a7bc4df02282f0f34d280df15d037b82c32003dabdffe76f536b2b067128",
        "ed25519_sig_R": "unmasked:32:0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5",
        "ed25519_sig_S": "unmasked:32:0x0b107a8e4341516524be5b59f0f55bd26bb4f91c70391ec6ac3ba3901582b85f",
        "ed25519_public_key": "unmasked:32:0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5",
    },
)
