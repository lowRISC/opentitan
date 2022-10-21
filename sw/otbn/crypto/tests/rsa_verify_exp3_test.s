/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */


.section .text.start

/**
 * Standalone RSA 1024 encrypt
 *
 * Uses OTBN modexp bignum lib to encrypt the message from the .data segment
 * in this file with the public key consisting of e=65537 and modulus from
 * .data segment in this file.
 *
 * Copies the encrypted message to wide registers for comparison (starting at
 * w0). See comment at the end of the file for expected values.
 */
run_rsa_verify_exp3:
  jal      x1, modexp_var
  /* pointer to out buffer */
  lw        x21, 28(x0)

  /* copy all limbs of result to wide reg file */
  li       x8, 0
  loop     x30, 2
    bn.lid   x8, 0(x21++)
    addi     x8, x8, 1

  ecall


.data

/*
 * The words below are used by the code above, but the linker can't tell
 * because we reference them by absolute address. Make a global symbol
 * (cfg_data), which will refer to the whole lot and ensure that gc-sections
 * doesn't discard them.
 */
.globl cfg_data
cfg_data:

/* exponent of the exponent (e') (Full exponent is e=2^e'+1) */
.word 0x00000001

/* number of limbs (N) */
.word 0x0000000C

/* pointer to m0' (dptr_m0d) */
.word 0x00000280

/* pointer to RR (dptr_rr) */
.word 0x000002c0

/* load pointer to modulus (dptr_m) */
.word 0x00000080

/* pointer to base bignum buffer (dptr_in) */
.word 0x000004c0

/* pointer to exponent buffer (dptr_exp, unused for encrypt) */
.word 0x000006c0

/* pointer to out buffer (dptr_out) */
.word 0x000008c0

/* Modulus */
.org 0x80
.word 0x3489eab3
.word 0x23e3d222
.word 0xbe69ae96
.word 0xccc537fa
.word 0xf83c6774
.word 0xe683f91b
.word 0x9c588896
.word 0x44654dec
.word 0x96729ce1
.word 0x625a6410
.word 0x6435e750
.word 0xec42933f
.word 0x130c9e34
.word 0xeb1834b6
.word 0x2a117689
.word 0xb3b2f7bf
.word 0x21f92171
.word 0x4c1a1765
.word 0x9a92fe4b
.word 0xac9b5286
.word 0x0049c14f
.word 0x2531d556
.word 0x3f6e28ae
.word 0xe12124a6
.word 0x40b11690
.word 0xecfb1d29
.word 0x9af61602
.word 0x3d0f71b9
.word 0x1b9246cf
.word 0xbe254ff6
.word 0xb2003ba0
.word 0x440c6682
.word 0x251589aa
.word 0xb65e34bb
.word 0x3c17861f
.word 0xc24717a0
.word 0x35588598
.word 0xf8b64e80
.word 0x71cd790b
.word 0xa7ba410a
.word 0x98ece611
.word 0x3502cc9b
.word 0xc75ac49f
.word 0x415dd4ee
.word 0x657989ed
.word 0x784146ac
.word 0x3d6dada5
.word 0xb59e1a7a
.word 0x4a97c7c6
.word 0xc52b7408
.word 0x269bfd6f
.word 0x48caa59f
.word 0x0a0e9ccf
.word 0xd8274c58
.word 0x34c920c7
.word 0x731753c9
.word 0xe258a425
.word 0x62ca945e
.word 0x7f200856
.word 0xae144df9
.word 0xbdd551af
.word 0xfed9fe6e
.word 0xd44e4c37
.word 0x47388b19
.word 0x576d7435
.word 0xc0765a63
.word 0xd8a3456f
.word 0x4ffd380b
.word 0xf99066a2
.word 0xc83187e8
.word 0xa17dfa22
.word 0x41a5e04a
.word 0x6b42c9bd
.word 0x65f90f0e
.word 0x73895904
.word 0x76b858bf
.word 0x1fd2a0db
.word 0x3aa32a9d
.word 0x642602f8
.word 0xa8fc97ea
.word 0xe5791ce9
.word 0xc061288e
.word 0xa20ed540
.word 0x0bcc76ac
.word 0x16031fd5
.word 0x2d000229
.word 0x54b087c4
.word 0x789ffa18
.word 0x25d78dc9
.word 0xc7b8caf1
.word 0x1d64086d
.word 0xbc0904be
.word 0x6a071710
.word 0xdce0936a
.word 0x569ca381
.word 0xb6a5ac8b

/* Montgomery constant m0' */
.org 0x280
.word 0x88df2b85
.word 0xd4626f97
.word 0x7f951ca7
.word 0xec3ab561
.word 0x711421b2
.word 0x6d7fb66f
.word 0x0811a625
.word 0x2c21c9d7

/* Squared Mongomery Radix RR = (2^3072)^2 mod N */
.org 0x2c0
.word 0x3863b1be
.word 0x2913ebf7
.word 0x4fc03d0e
.word 0x482a3973
.word 0xa3b8f6a9
.word 0xf7473acb
.word 0xbf4bd684
.word 0xa22a9423
.word 0x8d2fa6f6
.word 0x7f1acc71
.word 0x718c39ed
.word 0xffeaa651
.word 0xba592ce4
.word 0xa05e4c98
.word 0x89d5b580
.word 0x7f394220
.word 0xd02c350b
.word 0x71692df1
.word 0xf896a5b7
.word 0x791e5249
.word 0x0c7bf245
.word 0x80c8c8b2
.word 0x8bb7ca49
.word 0xc91f3f3a
.word 0x223bc9b1
.word 0x22b07bc8
.word 0xce145fbc
.word 0xa04cd67e
.word 0x3d7999d4
.word 0xaac652fc
.word 0x70380397
.word 0x7ad5512a
.word 0x605df8bb
.word 0x6e694ebf
.word 0x498901cb
.word 0x6966203d
.word 0x34ae90b6
.word 0x0859c604
.word 0x16b2ebaa
.word 0x44d734e0
.word 0x39caa18e
.word 0x76d1d9a3
.word 0x985570c8
.word 0xbd4216e8
.word 0x6ee8a815
.word 0xf45f6b13
.word 0xcafa40e9
.word 0xb8884042
.word 0xcda1fc24
.word 0x34e64f10
.word 0xeee01c26
.word 0x6b42d326
.word 0xe26972cd
.word 0x71f6230c
.word 0x27febf17
.word 0xdafc774b
.word 0x75777ad5
.word 0x6e5c4c40
.word 0x7995b95e
.word 0x2465f6f7
.word 0x6783399a
.word 0xe571421a
.word 0x8faf084a
.word 0xd303dd08
.word 0x92cc413e
.word 0x1029f59f
.word 0x08bec8f5
.word 0x8d3ae156
.word 0xbe3b3cae
.word 0x4a52fd6a
.word 0xc9979f63
.word 0x66dc5646
.word 0x315f0f71
.word 0xf867366a
.word 0x809ce4b1
.word 0xb69b56d3
.word 0xb0b219d7
.word 0xede105a6
.word 0xfc70656a
.word 0x7f27b7bd
.word 0x74e0004b
.word 0xe8bb9577
.word 0x2df61aba
.word 0x4ef701ea
.word 0x2d1f4d03
.word 0x17961c80
.word 0x7b01bded
.word 0x852a41bb
.word 0x5e173716
.word 0xf48a5071
.word 0x3dba1742
.word 0xa3a5c9ae
.word 0xfd275d1c
.word 0x2f3937f9
.word 0x45579413
.word 0x2951778f

/* signature */
.org 0x4c0
.word 0xca60cb6e
.word 0xd3a786de
.word 0x37623afb
.word 0x7f6cbc1a
.word 0x5366d957
.word 0xe69ffe2f
.word 0x3560dc40
.word 0xf8b205c5
.word 0xa612764f
.word 0xb0415cf7
.word 0x5c5b87d9
.word 0xe0081c67
.word 0xadc8d9bd
.word 0xdd072b18
.word 0x8e22b48b
.word 0x758b9df3
.word 0xb208d5ab
.word 0x5f1bcb08
.word 0xb16f9e88
.word 0xf2d37daf
.word 0xf7fc6ecb
.word 0x5a102bb9
.word 0xe61a9b3f
.word 0x96541e3e
.word 0x3718d3ef
.word 0x769b35c2
.word 0xf571f77a
.word 0x82a6f325
.word 0xaa5ef30c
.word 0x17048840
.word 0xc71ddc21
.word 0xc7bc71ed
.word 0x14f7ed74
.word 0x7a3d6a80
.word 0xebb0c73d
.word 0x5f28b2c2
.word 0x56a502db
.word 0x39a3814f
.word 0x37df9ba4
.word 0x397e700d
.word 0x6c03a24d
.word 0x9efa0232
.word 0x257c4b77
.word 0xa928a03a
.word 0x43455edd
.word 0x57e509fb
.word 0x32458a00
.word 0x09941f22
.word 0xca9af629
.word 0x76a01068
.word 0x4c638cbe
.word 0x9b8a3ff6
.word 0x3979752d
.word 0x6d4c9bb8
.word 0x3ee6189c
.word 0xab9b7212
.word 0x2116de70
.word 0x429344c4
.word 0x072412c7
.word 0x747fff3d
.word 0x9d07cc3f
.word 0xb188d846
.word 0xcf4959ed
.word 0xc622387c
.word 0x32aeb26b
.word 0xf2921d28
.word 0x60793032
.word 0x061e4108
.word 0x6d70682b
.word 0x062ffa0b
.word 0x2b1f1696
.word 0x507a26f5
.word 0x1401059c
.word 0x202485a9
.word 0xfe963ae9
.word 0x54423a9d
.word 0x9731f9bb
.word 0x227e9788
.word 0x50846b54
.word 0x1e9f59f1
.word 0x3f158119
.word 0xc36f0b7b
.word 0xbef3b349
.word 0xf9172b6f
.word 0x3daf21c0
.word 0x819ee37e
.word 0x0bba9299
.word 0x90727884
.word 0xc74908f9
.word 0xec095a40
.word 0x8e2120dd
.word 0xfbefd497
.word 0x2227f721
.word 0xb7abdc98
.word 0xf7e55656
.word 0x3be75b5c


/* Full key for reference:
   modulus                       n = 0xb6a5ac8b569ca381dce0936a6a071710bc0904be1d64086dc7b8caf125d78dc9789ffa1854b087c42d00022916031fd50bcc76aca20ed540c061288ee5791ce9a8fc97ea642602f83aa32a9d1fd2a0db76b858bf7389590465f90f0e6b42c9bd41a5e04aa17dfa22c83187e8f99066a24ffd380bd8a3456fc0765a63576d743547388b19d44e4c37fed9fe6ebdd551afae144df97f20085662ca945ee258a425731753c934c920c7d8274c580a0e9ccf48caa59f269bfd6fc52b74084a97c7c6b59e1a7a3d6dada5784146ac657989ed415dd4eec75ac49f3502cc9b98ece611a7ba410a71cd790bf8b64e8035588598c24717a03c17861fb65e34bb251589aa440c6682b2003ba0be254ff61b9246cf3d0f71b99af61602ecfb1d2940b11690e12124a63f6e28ae2531d5560049c14fac9b52869a92fe4b4c1a176521f92171b3b2f7bf2a117689eb1834b6130c9e34ec42933f6435e750625a641096729ce144654dec9c588896e683f91bf83c6774ccc537fabe69ae9623e3d2223489eab3
   private exponent              d = 0x1e70f217391a1b404f7ac33c67012e82ca0180ca5a3b56bcf69ecc7d864e97a1941aa9aeb8c816a0b22aab06d900854e2ca213c77057ce35756586c27b942f7c46d4c3fc660655d409c5dc6f854dc579e91eb9753dec3980bba982826735cc4a359ba561c594ff05cc0841517eed667062aa3401f9708b92a013b9bb393ce8b38bdec1d9a36262095524551274f8e2f29d0362543fdaac0e65cc6e0fd0641b5b932e8df6de218576a4068cb957026f77e1771b9a866f54e7f631e8ac0c6ea14b80c0e7c91cb13c916bc6189e79956f79cccc6d1e921ad67b72ae9ccf28593dc148e7fb42114d4a638a9fb6ee029e67873fc10cdd2914896ecdab80365ec3810e0de1a5ab64b7ea15de699fc14c8756e110a5cdbb58b5313d9c82b2e4c0860d670bfd31a7b01bd973a8b5a2756bd63e65310a128e3a3d6426b85f886ef3a3d23641c9533cb083e2af898e7523f61cd1981466b1895870f4aa8ce9d3c4cdf98cbaed118f4d29091c15fcf87ab572c55992b814ecacdfec2aca13e47956129c022b
   public exponent               e = 3
   squared Montgomery radix     RR = 0x2951778f455794132f3937f9fd275d1ca3a5c9ae3dba1742f48a50715e173716852a41bb7b01bded17961c802d1f4d034ef701ea2df61abae8bb957774e0004b7f27b7bdfc70656aede105a6b0b219d7b69b56d3809ce4b1f867366a315f0f7166dc5646c9979f634a52fd6abe3b3cae8d3ae15608bec8f51029f59f92cc413ed303dd088faf084ae571421a6783399a2465f6f77995b95e6e5c4c4075777ad5dafc774b27febf1771f6230ce26972cd6b42d326eee01c2634e64f10cda1fc24b8884042cafa40e9f45f6b136ee8a815bd4216e8985570c876d1d9a339caa18e44d734e016b2ebaa0859c60434ae90b66966203d498901cb6e694ebf605df8bb7ad5512a70380397aac652fc3d7999d4a04cd67ece145fbc22b07bc8223bc9b1c91f3f3a8bb7ca4980c8c8b20c7bf245791e5249f896a5b771692df1d02c350b7f39422089d5b580a05e4c98ba592ce4ffeaa651718c39ed7f1acc718d2fa6f6a22a9423bf4bd684f7473acba3b8f6a9482a39734fc03d0e2913ebf73863b1be
   Montgomery constant       m0inv = 0x468118b0b73114b22b37b480f5223ce79d8c695e44f9d7feae6d8747ab64a2e3d5bef3ff92e12a0bd0991ec4ce51d4403425247e409601732a860ad7adbfca840eb7c08bf2bda3d9ba65cbfb9e298d827ca479116700eab481933bf0bc4d09d99077ef3276b79066ddab13883d8f02d4a4592e13d9869353a26581ef88d52601b93c4337f3d1ec19b1eb9e58863344d38be53f29062cb0f4d6709586d29dedeae2a58841294a5fe2fcc9734a56aea4c10e82a7ff570c841e4ac15a3950e20a39a0bf581914ae8c00b0ed1644df6d2623c10b7977869a542d6c9958fb7a6695ed0e4e0e2798b3e149c4876ba5c2f02cfa6ec27b1ecb399f33a5dd45946c81a9ac9a6e1ef7dfa5c8d2eefc8af9f4ba8ec447fa654908fb78aeaed772d36c63cf58369abeeaf3ec5b48ba384dda0fba63a055e9e1d2d8068b200fcf15ce4d12b89654ac4dd294c04ee07207ff2801b3623cefc77abe66d238b9e010f1cd8d9f47e92c21c9d70811a6256d7fb66f711421b2ec3ab5617f951ca7d4626f9788df2b85
*/
