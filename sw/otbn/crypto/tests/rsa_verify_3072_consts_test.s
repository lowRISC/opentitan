/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone test for 3072 bit RSA Montgomery constant computation.
 *
 * Copies the message to wide registers for comparison (starting at
 * w0). See comment at the end of the file for expected values.
 */
run_rsa_verify_3072_consts_test:
  /* Compute m0_inv = (- (M^-1)) mod 2^256 */
  jal      x1, compute_m0_inv

  /* Compute R^2 = (2^3072)^2 mod M */
  jal      x1, compute_rr

  /* Copy m0_inv to w0 */
  li       x8, 0
  la       x21, m0inv
  bn.lid   x8++, 0(x21)

  /* copy all limbs of R^2 to wide reg file */
  la       x21, rr
  loopi    12, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall


.data

/* Modulus of test key */
.globl in_mod
in_mod:
  .word 0x6a6a75e1
  .word 0xa018ddc5
  .word 0x687bb168
  .word 0x8e8205a5
  .word 0x7dbfffa7
  .word 0xc8722ac5
  .word 0xf84d21cf
  .word 0xe1312531
  .word 0x0ce3f8a3
  .word 0xa825f988
  .word 0x57f51964
  .word 0xb27e206a
  .word 0x8e1dd008
  .word 0x1c4fb8d7
  .word 0x824fb142
  .word 0x1c8be7b3
  .word 0x7b9d6366
  .word 0xc56ad0f2
  .word 0xef762d5b
  .word 0x4b1431e3
  .word 0x8ae28eb9
  .word 0xd41db7aa
  .word 0x43cccdf7
  .word 0x91b74a84
  .word 0x80183850
  .word 0x30e74d0d
  .word 0xb62ed015
  .word 0x235574d2
  .word 0x8c28f251
  .word 0x4f40def2
  .word 0x24e2efdb
  .word 0x9ebd1ff2
  .word 0xfa7b49ee
  .word 0x2819a938
  .word 0x6e66b8c8
  .word 0x24e41546
  .word 0x4d783a7c
  .word 0xd2947d3d
  .word 0x1ab269e9
  .word 0xfad39f16
  .word 0xaab78f7b
  .word 0x49d8b510
  .word 0x35bf0dfb
  .word 0xeb274754
  .word 0x069eccc9
  .word 0xc13c437e
  .word 0xe3bc0f60
  .word 0xc9e0e12f
  .word 0xc253ac43
  .word 0x89c240e0
  .word 0xc4aba4e5
  .word 0xedf34bc0
  .word 0x5402c462
  .word 0x4021b0bd
  .word 0x996b6241
  .word 0xc3d9945f
  .word 0xa137ac60
  .word 0xf0250bf5
  .word 0xc8c7100f
  .word 0xb70d6b88
  .word 0x78916a8c
  .word 0x33370e5d
  .word 0x3970dcb9
  .word 0xaf4c58b4
  .word 0x5f78cb0d
  .word 0xb02d90b7
  .word 0xeb6c3d05
  .word 0x04afc71a
  .word 0x45185f0f
  .word 0x987caa5b
  .word 0x33976249
  .word 0x565afdbc
  .word 0x80a85056
  .word 0x59e07655
  .word 0x9a29e77d
  .word 0x7a8dfb7f
  .word 0x782e0204
  .word 0x4d6713ff
  .word 0x131000ea
  .word 0xe18e1206
  .word 0x21f57f30
  .word 0xf24f038b
  .word 0x59cf874d
  .word 0x24c50525
  .word 0xb52f170d
  .word 0x46c9adde
  .word 0x90e82c73
  .word 0x1344ceaf
  .word 0x663209f2
  .word 0x24bd4fbf
  .word 0x5e4ed04d
  .word 0x0fce770a
  .word 0x81f78793
  .word 0xa792e13e
  .word 0xa6c7bf58
  .word 0xe1df9be8

/* Output: Montgomery constant m0' */
.globl m0inv
m0inv:
.zero 32

/* Output: squared Mongomery Radix RR = (2^3072)^2 mod N */
.globl rr
rr:
.zero 384

/* Full key for reference:
   modulus                       n = 0xe1df9be8a6c7bf58a792e13e81f787930fce770a5e4ed04d24bd4fbf663209f21344ceaf90e82c7346c9addeb52f170d24c5052559cf874df24f038b21f57f30e18e1206131000ea4d6713ff782e02047a8dfb7f9a29e77d59e0765580a85056565afdbc33976249987caa5b45185f0f04afc71aeb6c3d05b02d90b75f78cb0daf4c58b43970dcb933370e5d78916a8cb70d6b88c8c7100ff0250bf5a137ac60c3d9945f996b62414021b0bd5402c462edf34bc0c4aba4e589c240e0c253ac43c9e0e12fe3bc0f60c13c437e069eccc9eb27475435bf0dfb49d8b510aab78f7bfad39f161ab269e9d2947d3d4d783a7c24e415466e66b8c82819a938fa7b49ee9ebd1ff224e2efdb4f40def28c28f251235574d2b62ed01530e74d0d8018385091b74a8443cccdf7d41db7aa8ae28eb94b1431e3ef762d5bc56ad0f27b9d63661c8be7b3824fb1421c4fb8d78e1dd008b27e206a57f51964a825f9880ce3f8a3e1312531f84d21cfc8722ac57dbfffa78e8205a5687bb168a018ddc56a6a75e1
   private exponent              d = 0x6041730707bffad6947efef72cdaa80f6f3e7cb351f2434984bd1a5585ff1006f5d82e3e5a41dee37748ae0c48e91ae93280b58b2fc545335dedf7241d222a045232c1928e20154bc41587cba852eef02aac03ffe25a3638d08adbd2df239b2cd7db29e34097243f19b912be176965e51809b28f51c14c15f6f8cc01a1317052d21ff67343414a06b081276184e66f622d060e8bf987ff5bd36a6e38cc6dd5cb5cdb05a461d485c829c4d1b5352e82b36814f4f4debb08e7fab769ff7e40bb19514af9168c9b773570c58f2c3e177edfe43d4e29ae72329a25d7da234ce73407d2619e5072dffbec1d9601446417d968de1e8772ce4b46fd5224cc0a6ddc889aedec8247de9a6b93f166df6981c487dc111b4eb0ec7bc15782db65570158da4523eab41c7455bd70c72a52e015a7cba482581bed16fef89213158c94f15592482069a742973b55372ced7d20dc9312980ce4696fa4d5715098c927fc12ab013af8df4b83869ef22b53c176f4a83b89cab93ce7f6e619ae0c59d7e511bebf06e3
   public exponent               e = 65537
   squared Montgomery radix     RR = 0x9e2dcea821e64d84fcb4969387993424eaee3c24785b7552b6988a4fa29196e27d0c0fc36ca4d02fb5822d5649619ddda277ef0ed19233b504e452fc37276997da9c946b472a10b49fe0c3630ad2fbbcba9fc09693718edca7e13295f8d074abb60788f6d9ee19c42966d4f8d21be300e4b83ed6514995dc2a9044a296cbf044524b09b77a58d0479774620afe4319c4f209e1234ce52e1d5c7070ff7516d8b74043add66878ec0dd9691ef573649941093520a20811a95fc509b5ca7a83d42a05f49af51ce689f5d9c77317ba59c5f5079883be4b4c22269bc14e3b234c8ff79849163aeabe1810c204b9ca0dbdc0cbce301343dd65e10898d8cc33c5b9a5be3d3d07f301dc7990ebc2405fe0112362c75cbb02879a18307e351549e642e25e90b209bf6c65ac0e6563c81a9ccd73f2b61eab77538c240e8aa862a9689a85bc32318a29f49dd5f776e77ababab5ae26da2e21031185bcae73f5cf6bcd410c5c546a7cfeeb165cd3d0f4fddadd38f5fbfb5be1e72c19d4ae9db9a2aca3eb77fa
   Montgomery constant       d0inv = 0x98a44f84397e684144214c83228ab43e1972189cbba34b5a4edbef91d022772d589d52b3b503299cf32a0c7b9aa9f8ed9c9c366b607da6fdb89991c29ccb146c2a85b6f413e358be5d5dc40e0aa492340f1f6d2a6eb015203f7b91bfe789377dfeed5e6ba3ea7bb2efeb980bce2895730b4b884748224db64040f5917fab212b3e8a289c370861d6760493e5323d6bf82669e60cd77df7f292c7833225f0b060359d1271ff80f3647dd87f7c876d545bdd643fd577de4ec7c80fe2308ecbd78cdaabc95e174c58c3b93cabc138c679a617c756ff3fb6fca8d912be11297cf059830b54188eb1161e1a7476270a3514789414cf662c4e04da7672f3ea877446b2996af70106f38a77aafcc273ff441e5f0fc30d8cef33be30b15cfe44727c0936dc64262c4c771d236ad834fefc6f3228def492fa69ece22f8cdd6115f0a5133e7da9803aadf07cd11406fb58bda827cfc90a25828f25ef9512e25f1fcdf1cc061dfc9779711cad8ba96ced374965995095d310b20b908e3bfd3e34f7f09b71df
*/
