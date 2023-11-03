# Crypto Library Tests

This folder contains test data and infrastructure for the OpenTitan
cryptographic library. Tests come from a variety of sources, including:
- Our own hard-coded tests and regression tests
- [wycheproof](https://github.com/google/wycheproof)
- Random tests
- Coming soon: FIPS tests!

The primary way of running crypto tests is to use the custom
`autogen_cryptotest_...` Bazel rules, which create build targets specialized to
different test sets.

**Note: New crypto tests should be written using the [cryptotest framework](cryptotest/README.md).**

## Setup

Each algorithm has a C test file (ending in `_functest.c`) which reads test
data from a header file (ending in `_testvectors.h`) and runs a set of tests on
each test vector. By default, the header file contains a small set of
hard-coded test vectors. If all you want to do is sanity-check, then simply run
`ninja` and run the `_functest` target (e.g.
`sw_lib_crypto_rsa_3072_verify_functest`) on your desired
platform.

However, if you want to run a set of test vectors from an external source, a
custom set of tests, or random tests, you'll need to populate the
`*_testvectors.h` header file with the tests you want to run. There is a Python
script for this for each algorithm, ending in `set_testvectors.py` (e.g.
`rsa_3072_verify_set_testvectors.py`). It reads an HJSON file containing your
test vectors, and writes a C header file containing the data in the format
expected from `*_testvectors.h". For test vectors from an external source, you
may need an extra script to parse the test vectors into the shared HJSON
format.

For example, here's the setup for just one algorithm, RSA-3072 verify:
```
tests/
  rsa_3072_verify_functest.c                 # Main test file
  rsa_3072_verify_set_testvectors.py         # Generates header from HJSON
  rsa_3072_verify_gen_random_testvectors.py  # Generates random test vectors
  testvectors/
    rsa_3072_verify_hardcoded.hjson          # Limited set of hard-coded tests
    wycheproof/
      rsa_3072_verify_parse_testvectors.py   # Parses raw test data to HJSON
    ...
```

### Adding New Hardcoded Tests

To add a new hardcoded test for some algorithm, simply edit the
`testvectors/{algorithm}_hardcoded.hjson` file. Bazel rules based on the
hardcoded tests will automatically pick up the changes.

### Adding New External Tests

If an external test data dependency such as wycheproof has been updated, there
should be no action required here unless file names have changed. The build
rules are designed to directly read external data from `sw/vendor` at build
time.

To add an entirely new test set, create a new folder under `testvectors/` and
write a script that reads the external data and translates tests into the
standardized HJSON format for that algorithm. Pass the script and input data to
an `autogen_cryptotest_hjson_external` build target.

### Example Direct Usage

To run the tests locally and manually (as opposed to via Bazel), see the
following examples.

Set up RSA-3072 test to run hardcoded test vectors:
```
$ ./rsa_3072_verify_set_testvectors.py testvectors/rsa_3072_verify_hardcoded.hjson
```
After this step, you can run `ninja` to re-build and then run the
`sw_lib_crypto_rsa_3072_verify_functest` target to run the
tests. The same applies to all other examples here.

Set up RSA-3072 test to run 20 random test vectors:
```
$ ./rsa_3072_verify_gen_random_testvectors.py 20 testvectors/rsa_3072_verify_random.hjson
$ ./rsa_3072_verify_set_testvectors.py testvectors/rsa_3072_verify_random.hjson rsa_3072_verify_testvectors.h
```

Set up RSA-3072 test to run a custom set of test vectors:
```
$ vim testvectors/custom_testvecs.hjson # write test vectors in HJSON format
$ ./rsa_3072_verify_set_testvectors.py testvectors/custom_testvecs.hjson
```

Set up RSA-3072 test to run all wycheproof test vectors:
```
$ testvectors/wycheproof/rsa_3072_verify_parse_testvectors.py\
  $REPO_TOP/sw/vendor/wycheproof/testvectors/rsa_signature_3072_sha256_test.json\
  testvectors/rsa_3072_verify_wycheproof.hjson
$ ./rsa_3072_verify_set_testvectors.py testvectors/rsa_3072_verify_wycheproof.hjson rsa_3072_verify_testvectors.h
```
