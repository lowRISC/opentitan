# Signing Guide

## Configuration of NitroKeys

> The following configuration only works in the `earlgrey_es_sival` branch.

NitroKeys are a personal security token used to hold the signing keys for
TEST and DEV devices.  NitroKeys can be used to sign tests and binaries for
devices in the TEST or DEV lifecycle states.

In order to sign with a NitroKey, you need to configure a profile for your
NitroKey.  The profile is defined by the keyset you want to use for signing.
The configuration should map the profile name to the specific token holding
the private key material for the named keyset.

For example, a configuration for `//sw/device/silicon_creator/rom/keys/real/rsa:keyset`
might look like the following:

>Locate this file in $HOME/.config/hsmtool/profiles.json and set the file
mode to 600.

```json
{
  "earlgrey_a0": {
    "token": "earlgrey_a0_000",
    "user": "user",
    "pin": "xxxxxx"
  }
}
```

## Signing with a token

> The following configuration only works in the `earlgrey_es_sival` branch.

Once a profile configuration is in place, you can build binaries signed by
the keyset by telling bazel that you want to use a token.

In the example below, we instruct bazel to use a NitroKey as the token
and to sign with the key specified by the `rsa_key` attribute of the target
(or the target's `exec_env`).

```console
bazel build --//signing:token=//signing/tokens:nitrokey //label-of-target
```

To sign with an alternate key, you can override the key label via the
keyset in question.  For `silicon_creator` code, the keyset is
`//sw/device/silicon_creator/rom/keys/real/rsa:keyset`.

```console
bazel build \
    --//signing:token=//signing/tokens:nitrokey \
    --//sw/device/silicon_creator/rom/keys/real/rsa:keyset=earlgrey_a0_dev_0 \
    //label-of-target
```

## Configuration for silicon\_owner SiVAL signing

The production SiVAL ROM\_EXT expects a signing key held in Google's cloud-kms
service.

You need an hsmtool profile that maps to the cloud-kms token.  Add an entry
to your profiles confiuration file:

>Locate this file in $HOME/.config/hsmtool/profiles.json and set the file
mode to 600.

```json
{
  "earlgrey_z0_sival": {
    "token": "ot-earlgrey-z0-sival",
    "user": "user"
  }
}
```

The configuration file may contain more than one token configuration, for
example:

```json
{
  "earlgrey_a0": {
    "token": "earlgrey_a0_000",
    "user": "user",
    "pin": "XXXXXX"
  },
  "earlgrey_z0_sival": {
    "token": "ot-earlgrey-z0-sival",
    "user": "user"
  }
}
```

### Cloud KMS authentication

In order to sign with the cloud-kms key, you need to authenticate to Google
cloud using your opentitan.org account.

> See additional instructions on how to install the `google-cloud-cli` package
for various OS distributions: https://cloud.google.com/sdk/docs/install.
>
>You may also want to consider using the snap package in Debian distributions:
https://cloud.google.com/sdk/docs/downloads-snap
>
> The `gcloud auth login` and `gcloud auth application-default login` commands
should open a webpage to select the account you want to use to login. The page
may take a while to load, and in some cases you may have to copy paste the URL
printed by the CLI into a browser to start the login process.
>
> Make sure to use your opentitan.org account to login.

```console
# Install the Google cloud CLI if you don't already have it.
sudo apt install -y google-cloud-cli

# Log into GCP using your opentitan.org credentials
gcloud auth login

# Application default authentication
gcloud auth application-default login
```

Once authenticated to Google cloud, you can build and sign SiVAL tests
by requesting the `cloud_kms_sival` token:

> You may have to update the permissions on the KMS configuration file as
follows:
>
> `chmod 600 signing/tokens/earlgrey_z1_sival.yaml`

```console
bazel build --//signing:token=//signing/tokens:cloud_kms_sival //label-of-target
```

## Demo of offline signing

This demonstration of the offline signing flow does not use an HSM.
It uses opentitantool to generate the image digests and to create the
detached signatures.  Finally, it attaches the signatures to the binaries
and emits signed artifacts.

### Generate pre-signing artifacts

Generating the pre-signing artifacts builds the requested targets and
updates the manifest and public key.  Then, SHA256 digests are computed
for each binary.

```console
bazel build //signing/examples:digests
```

The bazel `offline_presigning_artifacts` rule updates the binary with
a supplied manifest and public key:

```console
opentitantool \
   image manifest update \
   --manifest=<manifest file> \
   --key-file=<public key file> \
   --output=<pre-signed binary> \
   <original binary>
```

Having updated the manifest and public key, the rule then generates
the SHA256 digest to be signed:

```console
opentitantool \
   image digest \
   --bin=<sha256 digest> \
   <pre-signed binary>
```

### Generate the detached signatures

Normally, in this step, the pre-signing artifacts would be taken to the
secure facility and a signing ceremony would be performed to create the
detached signatures.

```console
bazel build //signing/examples:fake
```

The bazel `offline_fake_sign` rule performs the same RSA signing
operation as the HSM would perform, but public test keys are used
instead of the real keys:

```console
opentitantool \
   ecdsa sign \
   --input=<sha256 digest> \
   --output=<signed digest> \
   <private key file>
```

### Copy the signatures into into `signing/examples/signatures`

Normally, in this step, the signatures created in the signing ceremony
would be copied into the target directory.

```console
cp -f bazel-bin/signing/examples/*sig signing/examples/signatures/
```

### Attach signatures producing final signed binaries

The detached signatures are attached to the pre-signing binaries and
final signed binaries are produced.

```console
bazel build //signing/examples:signed
```

The bazel `offline_signature_attach` rule takes the signed digests and
attaches them to the pre-signed binaries, thus producing signed binaries
that can be verified by the ROM.

```console
opentitantool \
   image manifest update \
   --signature-file=<signed digest> \
   --output=<final signed binary> \
   <pre-signed binary>
```

### Inspect the signed artifacts (optional)

```console
cd $REPO_TOP
bazel run //sw/host/opentitantool -- \
   image manifest show \
   $PWD/bazel-bin/signing/examples/hello_world_fpga_cw310.signed.bin
```
