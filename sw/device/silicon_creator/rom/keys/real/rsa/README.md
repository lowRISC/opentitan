# Earlgrey A0 real keys

The keys in this subdirectory are the public components of earlgrey A0 `silicon_creator` keys.
They were generated during the HSM initialization ceremony on 2023-06-06.
The `hsmtool` command files are in the `hsmtool` subdirectory of this directory.
- The `earlgrey_keygen.hjson` file contains the RSA key generation commands and templates for the seven RSA keys in the ROM.
- The `earlgrey_pubkey_export.hjson` file contains the export commands to export the public keys as PKCS#1 DER files.
- The `earlgrey_test_signatures.hjson` file contains the signing directives to sign the message `test` with each of the keys so that the sigverify unit test in this directory can verify that the public key components have been included into the ROM correctly.

### Key Generation:

Key generation was performed with the following command after authenticating to the HSM using the vendor's `preload` utility.
```sh
hsmtool --token earlgrey_a0 -u user exec earlgrey_keygen.hjson
```

### Key Export:

Public key export was performed with the following command after authenticating to the HSM using the vendor's `preload` utility.
```sh
hsmtool --token earlgrey_a0 -u user exec earlgrey_pubkey_export.hjson
```

The public key DER files were converted to header files with `opentitantool`:
```sh
for f in *.der; do
    opentitantool rsa key export $f
done
```

### Test message signing:

Generating signatures for the test message was performed with the following command after authenticating to the HSM using the vendor's `preload` utility.
```sh
echo -n "test" >test.bin
hsmtool --token earlgrey_a0 -u user exec earlgrey_test_signatures.hjson
```

Each of the generated signature files was converted to C hex arrays in
`sigverify_rsa_keys_real_unittest.cc`:
```sh
for f in *.sig; do
    cat $f | xxd -p -c 4 | tac | sed 's|.*|0x&,|'
done
```
