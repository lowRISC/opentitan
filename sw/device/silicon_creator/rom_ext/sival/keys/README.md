# SiVAL owner and application keys

The keys in this directory are the owner and application keys for the SiVAL owner.
The private components of these keys are stored in CloudKMS in the `ot-earlgrey-z0-sival` keyring.

These keys were generated using the `gcloud` command line tool:

```bash
KEYS=(
    appkey_dev_0
    appkey_prod_0
    appkey_test_0
    ownership_owner_key
    ownership_activate_key
    ownership_unlock_key
)

for KEY in ${KEYS[@]}; do
    gcloud kms keys create ${KEY} \
        --keyring ot-earlgrey-z0-sival \
        --location us-west1 \
        --purpose "asymmetric-signing" \
        --default-algorithm "ec-sign-p256-sha256" \
        --protection-level hsm
done
```

The keys were then exported from CloudKMS using `hsmtool` and converted to C headers with `opentitantool`:

```bash
for KEY in ${KEYS[@]}; do
    hsmtool --token ot-earlgrey-z0-sival \
        ecdsa export \
        -l ${KEY} \
        -f der \
        sw/device/silicon_creator/rom_ext/sival/keys/${KEY}.der

    opentitantool ecdsa key export \
        sw/device/silicon_creator/rom_ext/sival/keys/${KEY}.der
done
```
