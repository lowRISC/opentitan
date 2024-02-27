/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Unified boot-services OTBN program.
 *
 * During the boot process, this program should remain loaded. This binary has
 * the following modes:
 *   1. MODE_SEC_BOOT_MODEXP: RSA-3072 modexp (to verify a code signature).
 *   2. MODE_ATTESTATION_KEYGEN: Derive a new attestation keypair (ECDSA-P256).
 *   3. MODE_ATTESTATION_ENDORSE: Sign with a saved attestation signing key.
 *   4. MODE_ATTESTATION_KEY_SAVE: Save an attestation signing key.
 *
 * Ibex will run `MODE_SEC_BOOT_MODEXP` as part of checking the code
 * signature of the next boot stage. This mode doesn't interact or interfere
 * with any other modes, and can be called at any point.
 *
 * The attestation modes are more entangled with each other. Part of the
 * purpose of this program is to store the attestation key of a particular key
 * manager stage long enough to sign the public key of the next stage, without
 * rebooting. At each key manager stage, Ibex should:
 *   - Call `MODE_ATTESTATION_KEYGEN` to get the current public key
 *   - Construct the attestation certificate for the current stage, including
 *     the public key
 *   - Call `MODE_ATTESTATION_ENDORSE` to sign the certificate with the stored
 *     signing key from the *previous stage* and clear the key
 *   - Call `MODE_ATTESTATION_KEY_SAVE` to save the current stage's signing
 *     key, which will later endorse the next stage's certificate
 *
 * Of course, in the first stage there is no previous stage signing key and no
 * certificate, so Ibex should skip the `MODE_ATTESTATION_ENDORSE` step. Ibex
 * may clear IMEM/DMEM if it needs to run a different OTBN routine (e.g.
 * signature verification for ownership transfer), but doing so will wipe any
 * saved keys. This binary is designed so that it should not need to be
 * cleared and re-loaded on a normal boot.
 *
 * The attestation keys are derived from a key manager seed value, which is
 * XORed with output from a specially seeded DRBG in order to satisfy the FIPS
 * 186-5 requirement that the seed comes from a DRBG (other FIPS documents say
 * it is permissible to XOR DRBG output with implementation-specific values, so
 * the key manager seed is effectively ignored for FIPS compliance).  The saved
 * signing key is stored in OTBN's scratchpad memory, which is not accessible
 * to Ibex over the bus.
 */

/**
 * Mode magic values, generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 4 -n 11 --avoid-zero -s 3357382482
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_SEC_BOOT_MODEXP, 0x7d3
.equ MODE_ATTESTATION_KEYGEN, 0x2bf
.equ MODE_ATTESTATION_ENDORSE, 0x5e8
.equ MODE_ATTESTATION_KEY_SAVE, 0x64d

.section .text.start
start:
  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_SEC_BOOT_MODEXP
  beq   x2, x3, sec_boot_modexp

  addi  x3, x0, MODE_ATTESTATION_KEYGEN
  beq   x2, x3, attestation_keygen

  addi  x3, x0, MODE_ATTESTATION_ENDORSE
  beq   x2, x3, attestation_endorse

  addi  x3, x0, MODE_ATTESTATION_KEY_SAVE
  beq   x2, x3, attestation_key_save

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * RSA-3072 modular exponentation.
 *
 * Computes msg = (sig^65537) mod M, where
 *          sig is the signature
 *          M is the public key modulus
 *
 * Uses the specialized RSA-3072 OTBN modexp implementation to recover an
 * encoded message from an input signature. Ibex needs to check that the
 * encoded message matches the encoding of the expected message to complete
 * signature verification.
 *
 * Assumes that the Montgomery constant m0_inv is provided, but computes the RR
 * constant on the fly. The only exponent supported is e=65537.
 *
 * @param[in] dmem[in_mod]: Modulus of the RSA public key
 * @param[in] dmem[rsa_inout]: Signature to check against
 * @param[in] dmem[m0inv]: Montgomery constant (-(M^-1)) mod 2^256
 * @param[out] dmem[rsa_inout]: Recovered message digest
 */
sec_boot_modexp:
  /* Compute R^2 (same for both exponents): dmem[rr] <= R^2 */
  jal      x1, compute_rr

  /* Set pointers to buffers for modexp. */
  la        x24, rsa_out
  la        x16, in_mod
  la        x23, rsa_in
  la        x26, rr
  la        x17, m0inv

  /* run modular exponentiation */
  jal      x1, modexp_var_3072_f4

  ecall

/**
 * Generate an attestation keypair from a sideloaded seed.
 *
 * Takes two input seeds, one from the key manager in the key-sideload slots
 * and one from DMEM that is expected to be the output of a DRBG and fully
 * independent from the first. For both seeds, only the first 320 bits are used
 * and the rest are ignored.
 *
 * @param[in]  dmem[attestation_additional_seed]: DRBG output.
 * @param[out]  dmem[x]: Public key x-coordinate.
 * @param[out]  dmem[y]: Public key y-coordinate.
 */
attestation_keygen:
  /* Initialize all-zero register. */
  bn.xor   w31, w31, w31

  /* Generate secret key in shares.
       w20, w21 <= d0 (first share of secret key)
       w10, w11 <= d1 (second share of secret key) */
  jal      x1, attestation_secret_key_from_seed

  /* Call scalar multiplication with base point.
     R = (x_p, y_p, z_p) = (w8, w9, w10) <= d*G */
  bn.mov    w0, w20
  bn.mov    w2, w10
  bn.mov    w1, w21
  bn.mov    w3, w11
  la        x21, p256_gx
  la        x22, p256_gy
  jal       x1, scalar_mult_int

  /* Convert masked result back to affine coordinates.
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

  /* Store public key in DMEM.
     dmem[x] <= x_a = w11
     dmem[y] <= y_a = w12 */
  li        x2, 11
  la        x21, x
  bn.sid    x2++, 0(x21)
  la        x22, y
  bn.sid    x2, 0(x22)

  ecall

/**
 * Sign a message using the saved signing key from the scratchpad.
 *
 * Clears the saved key after use, so only one signature is possible with a
 * saved key.
 *
 * @param[in]  dmem[msg]: Message digest (256 bits)
 * @param[in]   dmem[d0]: First share of private key d (320 bits)
 * @param[in]   dmem[d1]: Second share of private key d (320 bits)
 * @param[out]   dmem[r]: Buffer for r component of signature (256 bits)
 * @param[out]   dmem[s]: Buffer for s component of signature (256 bits)
 */
attestation_endorse:
  /* Generate a fresh random scalar for signing.
       dmem[k0] <= first share of k
       dmem[k1] <= second share of k */
  jal      x1, p256_generate_k

  /* Generate the signature.
       dmem[r], dmem[s] <= signature */
  jal      x1, p256_sign

  /* Clear the saved key by overwriting with random data.
       dmem[d0], dmem[d1] <= RND */
  li        x20, 20
  la        x2, d0
  bn.wsrr   w20, RND
  bn.sid    x20, 0(x2++)
  bn.wsrr   w20, RND
  bn.sid    x20, 0(x2)
  la        x2, d1
  bn.wsrr   w20, RND
  bn.sid    x20, 0(x2++)
  bn.wsrr   w20, RND
  bn.sid    x20, 0(x2)

  ecall

/**
 * Save an attestation signing key to the scratchpad.
 *
 * @param[in]  dmem[attestation_additional_seed]: DRBG output.
 * @param[out]  dmem[d0]: First share of private key (320 bits).
 * @param[out]  dmem[d1]: Second share of private key (320 bits).
 */
attestation_key_save:
  /* Initialize all-zero register. */
  bn.xor   w31, w31, w31

  /* Generate secret key in shares.
       w20, w21 <= d0 (first share of secret key)
       w10, w11 <= d1 (second share of secret key) */
  jal      x1, attestation_secret_key_from_seed

  /* Store secret key in DMEM.
     dmem[d0] <= w20, w21 = d0
     dmem[d1] <= w10, w11 = d1 */
  li        x2, 20
  la        x3, d0
  bn.sid    x2++, 0(x3)
  bn.sid    x2, 32(x3)
  li        x2, 10
  la        x3, d1
  bn.sid    x2++, 0(x3)
  bn.sid    x2, 32(x3)

  ecall

/**
 * Generate an attestation secret key from a sideloaded seed.
 *
 * Takes two input seeds, one from the key manager in the key-sideload slots
 * and one from DMEM that is expected to be the output of a DRBG and fully
 * independent from the first. For both seeds, only the first 320 bits are used
 * and the rest are ignored.
 *
 * Returns the key in two 320-bit shares d0 and d1, such that the secret key d
 * = (d0 + d1) mod n.
 *
 * @param[in]   w31: all-zero
 * @param[in]  dmem[attestation_additional_seed]: DRBG output seed
 * @param[out]  w20: Lower 256 bits of first share of secret key (d0)
 * @param[out]  w21: Upper 64 bits of first share of secret key (d0)
 * @param[out]  w10: Lower 256 bits of first share of secret key (d1)
 * @param[out]  w11: Upper 64 bits of second share of secret key (d1)
 *
 * clobbered registers: x2, x3, x20, w1 to w4, w10, w11, w20 to w29
 * clobbered flag groups: FG0
 */
attestation_secret_key_from_seed:
  /* Load keymgr seeds from WSRs.
       w20,w21 <= seed0
       w10,w11 <= seed1 */
  bn.wsrr  w20, KEY_S0_L
  bn.wsrr  w10, KEY_S1_L
  bn.wsrr  w21, KEY_S0_H
  bn.wsrr  w11, KEY_S1_H

  /* Load the additional DRBG seed from DMEM and XOR with one share of the
     sideloaded seed.
       w20, w21 <= seed0 ^ dmem[attestation_additional_seed] */
  la       x2, attestation_additional_seed
  li       x3, 22
  bn.lid   x3++, 0(x2)
  bn.xor   w20, w20, w22
  bn.lid   x3, 32(x2)
  bn.xor   w21, w21, w23

  /* Tail-call `p256_key_from_seed` to generate secret key shares.
       w20, w21 <= d0
       w10, w11 <= d1 */
  jal      x0, p256_key_from_seed

.bss

/* Operation mode. */
.globl mode
.balign 4
mode:
.zero 4

/* Input buffer for RSA-3072 modulus. */
.globl in_mod
.balign 32
in_mod:
.zero 384

/* Input buffer for precomputed RSA-3072 Montgomery constant:
      m0' = (- M) mod 2^256. */
.globl m0inv
.balign 32
m0inv:
.zero 32

/* Input buffer for RSA-3072 modexp: holds the signature. */
.globl rsa_in
.balign 32
rsa_in:
.zero 384

/* Output buffer for RSA-3072 modexp: holds the recovered message. */
.globl rsa_out
.balign 32
rsa_out:
.zero 384

/* Input buffer for an ECDSA-P256 message digest. */
.globl msg
.balign 32
msg:
.zero 32

/* Output buffer for the first part of an ECDSA-P256 signature. */
.globl r
.balign 32
r:
.zero 32

/* Output buffer for the second part of an ECDSA-P256 signature. */
.globl s
.balign 32
s:
.zero 32

/* ECDSA-P256 public key x-coordinate. */
.globl x
.balign 32
x:
.zero 32

/* ECDSA-P256 public key y-coordinate. */
.globl y
.balign 32
y:
.zero 32

/* DRBG output to XOR with key manager seed. */
.globl attestation_additional_seed
.balign 32
attestation_additional_seed:
.zero 64

.section .scratchpad

/* First share of the saved attestation ECDSA-P256 private key (d). */
.globl d0
.balign 32
d0:
.zero 64

/* Second share of the saved attestation ECDSA-P256 private key (d). */
.globl d1
.balign 32
d1:
.zero 64

/* First share of the per-signature ECDSA-P256 secret scalar (k). */
.globl k0
.balign 32
k0:
.zero 64

/* Second share of the per-signature ECDSA-P256 secret scalar (k). */
.globl k1
.balign 32
k1:
.zero 64

/* Buffer for the squared Mongomery Radix RR = (2^3072)^2 mod M.
   Populated by the RSA-3072 implementation. */
.balign 32
.globl rr
rr:
.zero 384
