Test vector generation for sigverify
------------------------------------

Code in this directory helps automatically generate test vectors for sigverify
based on JSON files. See the main crypto library for information on the format
and generation of these JSON files. The `sigverify_set_testvectors.py` script
is designed to read the exact same format.

Example:
```shell
$ ./sigverify_set_testvectors.py sw/device/tests/crypto/testvectors/rsa_3072_verify_wycheproof.hjson
```
