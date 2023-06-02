# Earlgrey A0 "mock" keys

The keys in this subdirectory are the "mock" earlgrey A0 keys -- they are not the real keys, but they will be replaced by the real keys when they are created.

The "mock" keys were created in the same way the real keys will be created: by using `hsmtool` to communicate with a PKCS#11 HSM to generate keys and then export the public components of those keys.

Key Generation:
```sh
hsmtool -t <token> -u user -p <pin> exec earlgrey_keygen.hjson
```

Key Export:
```sh
hsmtool -t <token> -u user -p <pin> exec earlgrey_pubkey_export.hjson
```
