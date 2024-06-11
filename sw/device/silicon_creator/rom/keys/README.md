## Re-generating fake/unauthorized ROM keys

The following steps generate a new fake test SPHINCS+ key pair and update the
various places that reference it. The instructions can be modified to generate
other types of keys:
- To generate ECDSA keys, replace every occurrence of `spx` with `ecdsa`.
- To generate prod or dev keys, replace every occurrenct of `test_key` with `prod_key` or `dev_key`.
- To generate unauthorized keys, use `keys/unauthorized` instead of `keys/fake`.

This process is only for fake keys. For real keys, use an offline HSM.

Build opentitantool:
```
bazel build //sw/host/opentitantool
```
Generate new key:
```
bazel-bin/sw/host/opentitantool/opentitantool spx key generate sw/device/silicon_creator/rom/keys/fake/spx/ test_key_0_spx
```
Manually fix data in the header file (in this case `sw/device/silicon_creator/rom/keys/fake/spx/test_key_0_spx.h`). Skip this step for unauthorized keys. This command prints the data in the right format:
```
cat sw/device/silicon_creator/rom/keys/fake/spx/test_key_0_spx.pub.pem | tail -n +2 | head -n -1 | base64 -d | hexdump -v -e '/4 "0x%08x, \\\n"'
```
Manually fix data in the OTP file (in this case `sw/device/silicon_creator/rom/keys/fake/otp/BUILD`). Skip this step for unauthorized keys. This command prints the data in close to the right format (you still need to add "0x"):
```
cat sw/device/silicon_creator/rom/keys/fake/spx/test_key_0_spx.pub.pem | tail -n +2 | head -n -1 | base64 -d | hexdump -v -e '/4 "%08x\n"' | tac | tr -d '\n'
```
