Test vectors in this file were pulled from the SPHINCS+ submission to round 3 of the NIST PQC competition.
This package does not seem to be accessible anywhere in git form, so it could not be vendored in the usual way.
It is downloadable from the SPHINCS+ website: https://sphincs.org/resources.html

Because the SPHINCS+ test vectors are so large, the parsing script includes the capability to separate a single KAT set into multiple HJSON files.
For example, parsing the 100 test vectors into 5 files of 20 tests each looks like:
```console
./parse_kat.py --num-tests=20  path/to/PQCsignKAT_64.rsp testvectors_kat.hjson
```

Alternatively, parsing all test vectors into one file looks like:
```console
./parse_kat.py path/to/PQCsignKAT_64.rsp testvectors_kat.hjson
```

For more usage details, try `./parse_kat.py -h`.
