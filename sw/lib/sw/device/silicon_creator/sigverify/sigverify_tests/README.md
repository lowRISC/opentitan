Test vector generation for sigverify
------------------------------------

Code in this directory helps automatically generate test vectors for sigverify
based on HJSON files. See the main crypto library for information on the format
and generation of these HJSON files. The `sigverify_set_testvectors.py` script
is designed to read the exact same format as the scripts in the main crypto
library.

Note that there is probably no need to run these scripts directly; the Bazel
`autogen_cryptotest_header` rule is the intended way of running different test
sets.

Example:
```shell
$ ./sigverify_set_testvectors.py sw/device/tests/crypto/testvectors/rsa_3072_verify_wycheproof.hjson
```
