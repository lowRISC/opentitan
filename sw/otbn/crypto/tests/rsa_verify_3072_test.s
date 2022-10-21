/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone test for 3072 bit RSA signature verification
 *
 * Uses the OTBN RSA 3072-bit only verification implementation to
 * obtain the message (digest) from a test signature.
 *
 * Copies the message to wide registers for comparison (starting at
 * w0). See comment at the end of the file for expected values.
 */
run_rsa_verify_3072:
  /* Set pointers to buffers. */
  la        x24, out_buf
  la        x16, in_mod
  la        x23, in_buf
  la        x26, rr
  la        x17, m0inv

  /* run modular exponentiation */
  jal      x1, modexp_var_3072_f4

  /* copy all limbs of result to wide reg file */
  la       x8, 0
  la       x21, out_buf
  loopi    12, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall


.data

/* Output buffer */
.globl out_buf
out_buf:
  .zero 384

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

/* Montgomery constant m0' */
.globl m0inv
m0inv:
.word 0xf09b71df
.word 0xfd3e34f7
.word 0x0b908e3b
.word 0x95d310b2
.word 0x49659950
.word 0xa96ced37
.word 0x711cad8b
.word 0x1dfc9779
.word 0xcdf1cc06
.word 0x12e25f1f
.word 0x8f25ef95
.word 0xc90a2582
.word 0xbda827cf
.word 0x1406fb58
.word 0xadf07cd1
.word 0x7da9803a

/* Squared Mongomery Radix RR = (2^3072)^2 mod N */
.globl rr
rr:
.word 0xa3eb77fa
.word 0x9db9a2ac
.word 0x2c19d4ae
.word 0xfb5be1e7
.word 0xdd38f5fb
.word 0xd0f4fdda
.word 0xeb165cd3
.word 0x546a7cfe
.word 0xcd410c5c
.word 0x73f5cf6b
.word 0x1185bcae
.word 0xda2e2103
.word 0xbab5ae26
.word 0x76e77aba
.word 0xf49dd5f7
.word 0x32318a29
.word 0x689a85bc
.word 0x8aa862a9
.word 0x538c240e
.word 0xb61eab77
.word 0x9ccd73f2
.word 0x6563c81a
.word 0x6c65ac0e
.word 0x90b209bf
.word 0xe642e25e
.word 0x7e351549
.word 0x879a1830
.word 0xc75cbb02
.word 0xe0112362
.word 0xebc2405f
.word 0x01dc7990
.word 0x3d3d07f3
.word 0xc5b9a5be
.word 0x98d8cc33
.word 0xdd65e108
.word 0xce301343
.word 0x0dbdc0cb
.word 0xc204b9ca
.word 0xeabe1810
.word 0x9849163a
.word 0x234c8ff7
.word 0x9bc14e3b
.word 0x4b4c2226
.word 0x079883be
.word 0xba59c5f5
.word 0xd9c77317
.word 0x1ce689f5
.word 0x05f49af5
.word 0x7a83d42a
.word 0xc509b5ca
.word 0x0811a95f
.word 0x093520a2
.word 0x73649941
.word 0xd9691ef5
.word 0x6878ec0d
.word 0x4043add6
.word 0x7516d8b7
.word 0x5c7070ff
.word 0x4ce52e1d
.word 0xf209e123
.word 0xfe4319c4
.word 0x9774620a
.word 0x7a58d047
.word 0x524b09b7
.word 0x96cbf044
.word 0x2a9044a2
.word 0x514995dc
.word 0xe4b83ed6
.word 0xd21be300
.word 0x2966d4f8
.word 0xd9ee19c4
.word 0xb60788f6
.word 0xf8d074ab
.word 0xa7e13295
.word 0x93718edc
.word 0xba9fc096
.word 0x0ad2fbbc
.word 0x9fe0c363
.word 0x472a10b4
.word 0xda9c946b
.word 0x37276997
.word 0x04e452fc
.word 0xd19233b5
.word 0xa277ef0e
.word 0x49619ddd
.word 0xb5822d56
.word 0x6ca4d02f
.word 0x7d0c0fc3
.word 0xa29196e2
.word 0xb6988a4f
.word 0x785b7552
.word 0xeaee3c24
.word 0x87993424
.word 0xfcb49693
.word 0x21e64d84
.word 0x9e2dcea8

/* signature */
.globl in_buf
in_buf:
.word 0xceb7e983
.word 0xe693b200
.word 0xf9153989
.word 0xcf899599
.word 0x1ec09fae
.word 0xf2f88007
.word 0x2a24eed5
.word 0x9c5b7c4e
.word 0x21a153b2
.word 0xaf7583ae
.word 0x04fdd694
.word 0x7550094b
.word 0xb2a69ac4
.word 0xe49d8022
.word 0x7ed6f162
.word 0x14bb3a1b
.word 0xbb29d8dd
.word 0x5c5815c2
.word 0x7a80d848
.word 0xb122f449
.word 0x59dca808
.word 0xbc1443e2
.word 0xe304ff93
.word 0xcc97ee4b
.word 0x42ef6b57
.word 0x1436839f
.word 0xae860b45
.word 0x6a843a17
.word 0x2381fb91
.word 0x09fd0635
.word 0xa431aac3
.word 0xd7220269
.word 0xdf3e2697
.word 0x35e2915e
.word 0xedba6956
.word 0x1d387448
.word 0x930006df
.word 0x961e5f00
.word 0xf2a7e960
.word 0x884e4add
.word 0x7dfe76b1
.word 0x4079aa79
.word 0x1f3a378d
.word 0x96c20697
.word 0x268aea57
.word 0x2c8569a4
.word 0x0474f512
.word 0x2388555c
.word 0x58679953
.word 0xe73da3a0
.word 0x43431b9a
.word 0x699f04d3
.word 0xfc0be066
.word 0xcce606f2
.word 0xd94cdfa0
.word 0x6c1ddca3
.word 0xe96c11f6
.word 0xfc635db4
.word 0x3bdb4f69
.word 0xa621c3e7
.word 0x9f292111
.word 0xb86e1e6b
.word 0xb74f923b
.word 0x592967a0
.word 0xc412097f
.word 0x8c1c8ca7
.word 0x494fcdb6
.word 0x87c5fe0f
.word 0x50c01aee
.word 0x8a26368e
.word 0xeaf12232
.word 0x7dade4d8
.word 0x39eb2ac6
.word 0x744f8aaa
.word 0xf34908ca
.word 0x1e0c656c
.word 0xe96d4e29
.word 0x8575d194
.word 0xe439bd31
.word 0xa74a77e3
.word 0x0f465b88
.word 0xf4e21152
.word 0x80400ad8
.word 0xe58501ec
.word 0xa29d7536
.word 0x55c19326
.word 0x9ebbc63e
.word 0x20c75aee
.word 0xef6783d7
.word 0x59ffdba5
.word 0x879b937b
.word 0x43a5c74c
.word 0x82b8f825
.word 0xfdf04b3a
.word 0x8fc62fbe
.word 0x114e6da5


/* Full key for reference:
   modulus                       n = 0xe1df9be8a6c7bf58a792e13e81f787930fce770a5e4ed04d24bd4fbf663209f21344ceaf90e82c7346c9addeb52f170d24c5052559cf874df24f038b21f57f30e18e1206131000ea4d6713ff782e02047a8dfb7f9a29e77d59e0765580a85056565afdbc33976249987caa5b45185f0f04afc71aeb6c3d05b02d90b75f78cb0daf4c58b43970dcb933370e5d78916a8cb70d6b88c8c7100ff0250bf5a137ac60c3d9945f996b62414021b0bd5402c462edf34bc0c4aba4e589c240e0c253ac43c9e0e12fe3bc0f60c13c437e069eccc9eb27475435bf0dfb49d8b510aab78f7bfad39f161ab269e9d2947d3d4d783a7c24e415466e66b8c82819a938fa7b49ee9ebd1ff224e2efdb4f40def28c28f251235574d2b62ed01530e74d0d8018385091b74a8443cccdf7d41db7aa8ae28eb94b1431e3ef762d5bc56ad0f27b9d63661c8be7b3824fb1421c4fb8d78e1dd008b27e206a57f51964a825f9880ce3f8a3e1312531f84d21cfc8722ac57dbfffa78e8205a5687bb168a018ddc56a6a75e1
   private exponent              d = 0x6041730707bffad6947efef72cdaa80f6f3e7cb351f2434984bd1a5585ff1006f5d82e3e5a41dee37748ae0c48e91ae93280b58b2fc545335dedf7241d222a045232c1928e20154bc41587cba852eef02aac03ffe25a3638d08adbd2df239b2cd7db29e34097243f19b912be176965e51809b28f51c14c15f6f8cc01a1317052d21ff67343414a06b081276184e66f622d060e8bf987ff5bd36a6e38cc6dd5cb5cdb05a461d485c829c4d1b5352e82b36814f4f4debb08e7fab769ff7e40bb19514af9168c9b773570c58f2c3e177edfe43d4e29ae72329a25d7da234ce73407d2619e5072dffbec1d9601446417d968de1e8772ce4b46fd5224cc0a6ddc889aedec8247de9a6b93f166df6981c487dc111b4eb0ec7bc15782db65570158da4523eab41c7455bd70c72a52e015a7cba482581bed16fef89213158c94f15592482069a742973b55372ced7d20dc9312980ce4696fa4d5715098c927fc12ab013af8df4b83869ef22b53c176f4a83b89cab93ce7f6e619ae0c59d7e511bebf06e3
   public exponent               e = 65537
   squared Montgomery radix     RR = 0x9e2dcea821e64d84fcb4969387993424eaee3c24785b7552b6988a4fa29196e27d0c0fc36ca4d02fb5822d5649619ddda277ef0ed19233b504e452fc37276997da9c946b472a10b49fe0c3630ad2fbbcba9fc09693718edca7e13295f8d074abb60788f6d9ee19c42966d4f8d21be300e4b83ed6514995dc2a9044a296cbf044524b09b77a58d0479774620afe4319c4f209e1234ce52e1d5c7070ff7516d8b74043add66878ec0dd9691ef573649941093520a20811a95fc509b5ca7a83d42a05f49af51ce689f5d9c77317ba59c5f5079883be4b4c22269bc14e3b234c8ff79849163aeabe1810c204b9ca0dbdc0cbce301343dd65e10898d8cc33c5b9a5be3d3d07f301dc7990ebc2405fe0112362c75cbb02879a18307e351549e642e25e90b209bf6c65ac0e6563c81a9ccd73f2b61eab77538c240e8aa862a9689a85bc32318a29f49dd5f776e77ababab5ae26da2e21031185bcae73f5cf6bcd410c5c546a7cfeeb165cd3d0f4fddadd38f5fbfb5be1e72c19d4ae9db9a2aca3eb77fa
   Montgomery constant       d0inv = 0x98a44f84397e684144214c83228ab43e1972189cbba34b5a4edbef91d022772d589d52b3b503299cf32a0c7b9aa9f8ed9c9c366b607da6fdb89991c29ccb146c2a85b6f413e358be5d5dc40e0aa492340f1f6d2a6eb015203f7b91bfe789377dfeed5e6ba3ea7bb2efeb980bce2895730b4b884748224db64040f5917fab212b3e8a289c370861d6760493e5323d6bf82669e60cd77df7f292c7833225f0b060359d1271ff80f3647dd87f7c876d545bdd643fd577de4ec7c80fe2308ecbd78cdaabc95e174c58c3b93cabc138c679a617c756ff3fb6fca8d912be11297cf059830b54188eb1161e1a7476270a3514789414cf662c4e04da7672f3ea877446b2996af70106f38a77aafcc273ff441e5f0fc30d8cef33be30b15cfe44727c0936dc64262c4c771d236ad834fefc6f3228def492fa69ece22f8cdd6115f0a5133e7da9803aadf07cd11406fb58bda827cfc90a25828f25ef9512e25f1fcdf1cc061dfc9779711cad8ba96ced374965995095d310b20b908e3bfd3e34f7f09b71df
*/
