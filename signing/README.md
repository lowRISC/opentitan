# Demo of offline signing

This demonstration of the offline signing flow does not use an HSM.
It uses opentitantool to generate the image digests and to create the
detached signatures.  Finally, it attaches the signatures to the binaries
and emits signed artifacts.

1. Generate pre-signing artifacts:

   ```
   bazel build //siging/examples:digests
   ```

2. Generate the detached signatures.

   Normally, in this step, the pre-signing artifacts would be taken
   to the secure facility and a signing ceremony would be performed to
   create the detached signatures.

   ```
   bazel build //siging/examples:fake
   ```

3. Copy the signatures into into `signing/examples/signatures`

   Normally, in this step, the signatures created in the signing ceremony
   would be copied into the target directory.

   ```
   cp -f bazel-bin/signing/examples/*.sig signing/examples/signatures/
   ```

4. Attach signatures to the pre-signed binaries, thus generating
   signed binaries:

   ```
   bazel build //signing/rom_ext:signed
   ```

5. Inspect the signed artifacts (optional):

   ```
   cd $REPO_TOP
   bazel run //sw/host/opentitantool -- \
       image manifest show \
       $PWD/bazel-bin/signing/examples/hello_world_fpga_cw310.signed.bin
   ```
