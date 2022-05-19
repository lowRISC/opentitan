# Demo of offline signing

This demonstration of the offline signing flow does not use an HSM.
It uses opentitantool to generate the image digests and to create the
detached signatures.  Finally, it attaches the signatures to the binaries
and emits signed artifacts.

## Generate pre-signing artifacts

Generating the pre-signing artifacts builds the requested targets and
updates the manifest and public key.  Then, SHA256 digests are computed
for each binary.
```
bazel build //siging/examples:digests
```

The bazel `offline_presigning_artifacts` rule updates the binary with
a supplied manifest and public key:
```
opentitantool \
   image manifest update \
   --manifest=<manifest file> \
   --key-file=<public key file> \
   --output=<pre-signed binary> \
   <original binary>
```

Having updated the manifest and public key, the rule then generates
the SHA256 digest to be signed:
```
opentitantool \
   image digest \
   --bin=<sha256 digest> \
   <pre-signed binary>
```

## Generate the detached signatures

Normally, in this step, the pre-signing artifacts would be taken to the
secure facility and a signing ceremony would be performed to create the
detached signatures.

```
bazel build //siging/examples:fake
```

The bazel `offline_fake_sign` rule performs the same RSA signing
operation as the HSM would perform, but public test keys are used
instead of the real keys:
```
opentitantool \
   rsa sign \
   --input=<sha256 digest> \
   --output=<signed digest> \
   <private key file>
```

## Copy the signatures into into `signing/examples/signatures`

Normally, in this step, the signatures created in the signing ceremony
would be copied into the target directory.

```
cp -f bazel-bin/signing/examples/*.sig signing/examples/signatures/
```

## Attach signatures producing final signed binaries

The detached signatures are attached to the pre-signing binaries and
final signed binaries are produced.

```
bazel build //signing/examples:signed
```

The bazel `offline_signature_attach` rule takes the signed digests and
attaches them to the pre-signed binaries, thus producing signed binaries
that can be verified by the ROM.
```
opentitantool \
   image manifest update \
   --signature-file=<signed digest> \
   --output=<final signed binary> \
   <pre-signed binary>
```

## Inspect the signed artifacts (optional)

```
cd $REPO_TOP
bazel run //sw/host/opentitantool -- \
   image manifest show \
   $PWD/bazel-bin/signing/examples/hello_world_fpga_cw310.signed.bin
```
