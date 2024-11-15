# SiVAL owner and application keys

The keys in this directory are the owner and application keys for the SiVAL owner.
The private components of these keys are stored in CloudKMS in the `ot-earlgrey-a1-sival` keyring.

These keys were generated using the `gcloud` tool and exported with `hsmtool`:

```bash
KEYRING=ot-earlgrey-a1-sival
KEYS=(
    sv00-app-key-prod-0
    sv00-app-key-dev-0
    sv00-app-key-test-0
    sv00-ownership-owner-0
    sv00-ownership-activate-0
    sv00-ownership-unlock-0
)

### Generate Keys
for KEY in ${KEYS[@]}; do
    gcloud kms keys create ${KEY} \
        --keyring ${KEYRING} \
        --location us-west1 \
        --purpose "asymmetric-signing" \
        --default-algorithm "ec-sign-p256-sha256" \
        --protection-level hsm
done

### Export public keys
# From https://github.com/GoogleCloudPlatform/kms-integrations/releases/tag/pkcs11-v1.2
export HSMTOOL_MODULE=$(pwd)/libkmsp11.so
export KMS_PKCS11_CONFIG=${KEYRING}.yaml

cat >${KEYRING}.yaml <<EOT
---
tokens:
  - key_ring: "projects/otkms-407107/locations/us-west1/keyRings/${KEYRING}"
    label: "${KEYRING}"
log_directory: "/tmp"
EOT

for KEY in ${KEYS[@]}; do
    hsmtool --token ${KEYRING} \
        ecdsa export \
        -l ${KEY} \
        -f der \
        ${KEY}.pub.der
done
```
