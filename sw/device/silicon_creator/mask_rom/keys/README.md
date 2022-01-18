---
title: "Signing Keys"
---

This directory contains ASN1 DER encoded development keys for signing ROM\_EXT
images. Until we have a more ergonomic tool for working with keys and signatures,
below snippets can be used for various operations.

Generating a key pair:
```
$ openssl genrsa -out <basename>.pem -f4 3072
Generating RSA private key, 3072 bit long modulus (2 primes)
..............................++++
.....................................................................++++
e is 3 (0x03)

$ openssl rsa -outform DER -in <basename>.pem -out <basename>.private.der
writing RSA key

$ openssl rsa -outform DER -in <basename>.pem -pubout -out <basename>.public.der
writing RSA key
```

Inspecting a key:
```
$ openssl rsa -inform DER -pubin -in <basename>.public.der -modulus -noout
Modulus=DA81748B9EEBE1E6FABE9ACB1C0A...

$ openssl rsa -inform DER -pubin -in <basename>.public.der -noout -text
RSA Public-Key: (3072 bit)
Modulus:
    00:da:81:74:8b:9e:eb:e1:e6:fa:be:9a:cb:1c:0a:
    ...
    e0:2f:43:dd:47:25:8f:e1:4b:15
Exponent: 3 (0x3)
```

Calculating the digest of a message:
```
$ echo -n "test" | openssl dgst -sha256
(stdin)= 9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08
```

Signing a message:
```
$ echo -n "test" | openssl dgst -sha256 -keyform DER -sign <basename>.private.der -hex
(stdin)= ad46cc63c05f66deb638476a7d...
```

Verifying a signature:
```
$ echo -n "test" | openssl dgst -sha256 -keyform DER -sign <basename>.private.der -out test_sig
$ echo -n "test" | openssl dgst -sha256 -keyform DER -verify <basename>.public.der -signature test_sig
Verified OK
```

Printing the encoded message during signature verification:
```
$ openssl rsautl -verify -in test_sig -inkey <basename>.public.der -pubin -keyform DER -raw -hexdump
0000 - 00 01 ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0010 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0020 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0030 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0040 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0050 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0060 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0070 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0080 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0090 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00a0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00b0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00c0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00d0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00e0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
00f0 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0100 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0110 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0120 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0130 - ff ff ff ff ff ff ff ff-ff ff ff ff ff ff ff ff   ................
0140 - ff ff ff ff ff ff ff ff-ff ff ff ff 00 30 31 30   .............010
0150 - 0d 06 09 60 86 48 01 65-03 04 02 01 05 00 04 20   ...`.H.e.......
0160 - 9f 86 d0 81 88 4c 7d 65-9a 2f ea a0 c5 5a d0 15   .....L}e./...Z..
0170 - a3 bf 4f 1b 2b 0b 82 2c-d1 5d 6c 15 b0 f0 0a 08   ..O.+..,.]l.....
```

Please note that `openssl` outputs are big-endian while OpenTitan signature
verification uses little-endian representation. Therefore, outputs of the commands
above should be converted to little-endian before they can be used in tests or
source code. One way to do this (until we have a more ergonomic way) is to pipe
binary outputs to `xxd -p -c 4 | tac`:
```
$ echo -n "test" | openssl dgst -sha256 -binary | xxd -p -c 4 | tac
b0f00a08
d15d6c15
2b0b822c
a3bf4f1b
c55ad015
9a2feaa0
884c7d65
9f86d081
```
