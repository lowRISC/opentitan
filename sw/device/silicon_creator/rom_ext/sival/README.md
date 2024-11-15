# SiVAL ROM\_EXT

The ROM\_EXT build in this directory is for chips that are configured as the SiVAL SKU.

The SiVAL SKU is initialized with the SiVAL owner during provisioning.
The human-readable owner configuration is `sival_owner.json5` and is translated to binary form with the following command:

```bash
cd $REPO_TOP
opentitantool ownership config \
    --input sw/device/silicon_creator/rom_ext/sival/sival_owner.json5 \
    sw/device/silicon_creator/rom_ext/sival/sival_owner.bin
```

The configuration is signed using the owner key stored in the Cloud KMS keyring `ot-earlgrey-a1-sival`:

```bash
cd $REPO_TOP

# From https://github.com/GoogleCloudPlatform/kms-integrations/releases/tag/pkcs11-v1.2
export HSMTOOL_MODULE=$(pwd)/libkmsp11.so
export KMS_PKCS11_CONFIG=signing/tokens/ot-earlgrey-a1-sival.yaml

hsmtool -t ot-earlgrey-a1-sival ecdsa sign \
    -l sv00-ownership-owner-0 \
    --little-endian \
    --format=slice:0..1952 \
    --update-in-place=1952..2016 \
    sw/device/silicon_creator/rom_ext/sival/sival_owner.bin
```

The header file `sival_owner.h` was created by dumping the binary file to a C header.
This file is only used by the "fake" ROM\_EXT used in testing FPGA configurations.
NOTE: the repeating unused data pattern `ZZZZ` can be cut out of the hexdump as the `sku_creator_owner_init` function will fill the unused portion of the owner page with that pattern.
```bash
cd $REPO_TOP

./util/sh/scripts/bin2c.sh \
    --input sw/device/silicon_creator/rom_ext/sival/sival_owner.bin \
    --output sw/device/silicon_creator/rom_ext/sival/sival_owner.h \
    --name sival_owner
```
