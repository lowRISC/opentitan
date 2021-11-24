# Crypto Library Tests

This folder contains test data and infrastructure for the OpenTitan
cryptographic library. Tests come from a variety of sources, including:
- Our own hard-coded tests and regression tests
- Coming soon: [wycheproof](https://github.com/google/wycheproof)
- Coming soon: random tests!
- Coming soon: FIPS tests!

## Setup

Each algorithm has a C test file (ending in `_functest.c`) which reads test
data from a header file (ending in `_testvectors.h`) and runs a set of tests on
each test vector. By default, the header file contains a small set of
hard-coded test vectors. If all you want to do is sanity-check, then simply run
`ninja` and run the `_functest` target (e.g.
`sw_silicon_creator_lib_crypto_rsa_3072_verify_functest`) on your desired
platform.

However, if you want to run a set of test vectors from an external source, a
custom set of tests, or random tests, you'll need to populate the
`*_testvectors.h` header file with the tests you want to run. There is a Python
script for this for each algorithm, ending in `set_testvectors.py` (e.g.
`rsa_3072_verify_set_testvectors.py`). It reads an HJSON file containing your
test vectors, and writes a C header file containing the data in the format
expected from `*_testvectors.h".

For example, here's the setup for just one algorithm, RSA-3072 verify:
```
tests/
  rsa_3072_verify_functest.c                 # Main test file
  rsa_3072_verify_testvectors.h              # Test vectors (auto-generated)
  rsa_3072_verify_set_testvectors.py         # Generates .h above
  testvectors/
    rsa_3072_verify_hardcoded.hjson          # Limited set of hard-coded tests
    wycheproof/
      rsa_3072_verify_parse_testvectors.py   # Parses raw test data to HJSON
      raw/
        rsa_signature_3072_sha256_test.json  # Raw test data
    ...
```

### Example Usage

Set up RSA-3072 test to run hardcoded test vectors:
```
$ ./rsa_3072_verify_set_testvectors.py testvectors/rsa_3072_verify_hardcoded.hjson
```
After this step, you can run `ninja` to re-build and then run the
`sw_silicon_creator_lib_crypto_rsa_3072_verify_functest` target to run the
tests. The same applies to all other examples here.

Set up RSA-3072 test to run a custom set of test vectors:
```
$ vim testvectors/custom_testvecs.hjson # write test vectors in HJSON format
$ ./rsa_3072_verify_set_testvectors.py testvectors/custom_testvecs.hjson
```

Set up RSA-3072 test to run all wycheproof test vectors:
```
$ ./testvectors/wycheproof/rsa_3072_verify_parse_testvectors.py > testvectors/rsa_3072_verify_wycheproof.hjson
$ ./rsa_3072_verify_set_testvectors.py testvectors/rsa_3072_verify_wycheproof.hjson
```
