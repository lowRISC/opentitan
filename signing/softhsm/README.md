# SoftHSM2 Configuration

This is a basic SoftHSM2 configurtion for testing signing flows with fake keys.

The configuration was created via:

```
export SOFTHSM2_CONF=signing/softhsm/softhsm.conf
softhsm2-util --init-token --label fake_keys --so-pin officer_pin --pin 123456 --free

```

Where `softhsm-util` is one of the binaries emitted by the `@softhsm2//:softhsm2` target.
