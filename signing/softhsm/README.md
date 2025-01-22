# SoftHSM2 Configuration

This is a basic SoftHSM2 configuration for testing signing flows with fake keys.

The configuration was created via:

```
export SOFTHSM2_CONF=signing/softhsm/softhsm.conf
softhsm2-util --init-token --label fake_keys --so-pin officer_pin --pin 123456 --free

```

Where `softhsm-util` is one of the binaries emitted by the `@softhsm2//:softhsm2` target.

## Keys

The softhsm instance contains a few keys needed for testing.  These were
imported with hsmtool.

```
export HSMTOOL_MODULE=bazel-out/k8-fastbuild/bin/external/softhsm2/softhsm2/lib/softhsm/libsofthsm2.so
export HSMTOOL_SPX_MODULE=pkcs11-ef
export SOFTHSM2_CONF=signing/softhsm/softhsm.conf

hsmtool -t fake_keys -u user -p 123456 \
    ecdsa import --label fake_app_prod_ecdsa \
    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.der

hsmtool -t fake_keys -u user -p 123456 \
    spx import --label fake_app_prod_spx \
    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_spx.pem
```
