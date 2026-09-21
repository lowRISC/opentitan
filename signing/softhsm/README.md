# SoftHSM2 Configuration

This is a basic SoftHSM2 configuration for testing signing flows with fake keys.

As of the time of writing, we import some SLH-DSA keys into our SoftHSM instance.
Upstream SoftHSM2 does not currently support SLH-DSA, so there are some patches maintained under `third_party/hsm/patches/*` that vendor in and extend proposed upstream patches to add SLH-DSA support.
If you are using an unpatched SoftHSM instance, the below commands relating to `hsmtool slh-dsa` will not function, and should be skipped.

## Initialization

The configuration was created via:

```sh
# Run these commands from the root of the OpenTitan repository, as we're passing
# in some relative paths, and SoftHSM2 can be finicky in resolving them.
bazel build @softhsm2//:softhsm2

export SOFTHSM2_CONF=signing/softhsm/softhsm.conf
export SOFTHSM_MODULE=$(bazel cquery @softhsm2//:softhsm2 | grep libsofthsm2.so | xargs realpath)
$(bazel cquery @softhsm2//:softhsm2 | grep softhsm2-util) \
    --module=${SOFTHSM_MODULE} \
    --init-token --label fake_keys --so-pin officer_pin --pin 123456 --free
```

## Keys

The SoftHSM token contains a few keys needed for testing.
These were imported with [hsmtool](../../sw/host/hsmtool/README.md), as described below:

```sh
# Run these commands from the root of the OpenTitan repository.
# The `SOFTHSM2_CONF` configuration file encodes a relative `tokendir`, and so
# it will complain if hsmtool is being run via Bazel and not from the CWD.
bazel build //sw/host/hsmtool
cp $(bazel cquery //sw/host/hsmtool | grep "hsmtool$") hsmtool
bazel build @softhsm2//:softhsm2

export SOFTHSM2_CONF=signing/softhsm/softhsm.conf
export HSMTOOL_MODULE=$(bazel cquery @softhsm2//:softhsm2 | grep libsofthsm2.so | xargs realpath)
export HSMTOOL_SPX_MODULE=pkcs11-ef
export HSMTOOL_TOKEN=fake_keys
export HSMTOOL_USER=user
export HSMTOOL_PIN=123456

# Importing just the ECDSA, SPHINCS+ and SLH-DSA private keys is sufficient
# -- ECDSA public keys can be calculated from the private key, and SPHINCS+/
# SLH-DSA embeds the public key components into their private keys. Also,
# the SPHINCS+ key is just stored as `CKO_DATA` due to not being standardized.
./hsmtool ecdsa import --label fake_app_prod_ecdsa \
    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.der
./hsmtool spx import --label fake_app_prod_spx \
    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_spx.pem
./hsmtool slh-dsa import --label fake_app_prod_slh_dsa \
    sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_slh_dsa.pem

# For testing DICE ML-DSA, there is also a seed imported (again as `CKO_DATA`).
./hsmtool object write --label fake_dice_mldsa_seed \
    sw/device/silicon_creator/manuf/keys/fake/sk_mldsa.pkcs8.der
```

You can then check that the tokens have been correctly imported using `./hsmtool object show`.
The output should look something like the below (with different `CKA_ID` values):

```json
{
  "objects": [
    {
      "CKA_LABEL": "fake_app_prod_spx",
      "CKA_CLASS": "CKO_DATA"
    },
    {
      "CKA_ID": "5C:6C:FC:A4:50:14:0F:73",
      "CKA_LABEL": "fake_app_prod_slh_dsa",
      "CKA_CLASS": "CKO_PRIVATE_KEY",
      "CKA_KEY_TYPE": "CKK_SLH_DSA"
    },
    {
      "CKA_ID": "5C:53:F0:B7:AB:0F:C0:1A",
      "CKA_LABEL": "fake_app_prod_ecdsa",
      "CKA_CLASS": "CKO_PRIVATE_KEY",
      "CKA_KEY_TYPE": "CKK_EC"
    },
    {
      "CKA_ID": "5C:6C:FC:A4:50:14:0F:73",
      "CKA_LABEL": "fake_app_prod_slh_dsa",
      "CKA_CLASS": "CKO_PUBLIC_KEY",
      "CKA_KEY_TYPE": "CKK_SLH_DSA"
    },
    {
      "CKA_LABEL": "fake_dice_mldsa_seed",
      "CKA_CLASS": "CKO_DATA"
    },
    {
      "CKA_ID": "5C:53:F0:B7:AB:0F:C0:1A",
      "CKA_LABEL": "fake_app_prod_ecdsa",
      "CKA_CLASS": "CKO_PUBLIC_KEY",
      "CKA_KEY_TYPE": "CKK_EC"
    }
  ]
}
```
