# Earlgrey A2 ROM binaries

This directory contains the ROM binaries released for the Earlgrey A2 silicon
revision.

The binaries (except for the QEMU variant) are based on the
`Earlgrey-PROD-A2-M6-ROM-RC1` tag.

The QEMU binaries are built with the qemu PR
(https://github.com/lowRISC/opentitan/pull/26124) cherry-picked on top of the
same tag.


## Reproduction Instructions

```bash
#!/bin/bash

mkdir -p /tmp/a2rom/
chmod +w /tmp/a2rom/*
rm -f /tmp/a2rom/*

git add -A && git reset --hard
git checkout -d Earlgrey-PROD-A2-M6-ROM-RC1

ROM_DIR="bazel-bin/sw/device/silicon_creator/rom/"

./bazelisk.sh clean --async
./bazelisk.sh build --stamp //sw/device/silicon_creator/rom:mask_rom
ls -l "$ROM_DIR"/mask_rom_*.{elf,39.scr.vmem}
cp "$ROM_DIR"/mask_rom_*.{elf,39.scr.vmem} /tmp/a2rom/
chmod 644 /tmp/a2rom/*

# Cherrypick https://github.com/lowRISC/opentitan/pull/26124
# (first 4 commits)
git cherry-pick --no-commit \
  a2fff1f628735a4993ce9b568a8042e4e2550581 \
  b9de775e9497fa0d860863f90f70d69120a8f297 \
  66b004a2b92b3273a1c46c18a211a87b06779145 \
  304ac8d6ae1b5e1b5a4e3b8a16516fb98ce51ff7

./bazelisk.sh clean --async
./bazelisk.sh build --stamp //sw/device/silicon_creator/rom:mask_rom
ls -l "$ROM_DIR"/mask_rom_sim_qemu_*.elf
cp "$ROM_DIR"/mask_rom_sim_qemu_*.elf /tmp/a2rom/
chmod 644 /tmp/a2rom/*

# Cleanup cherrypick
git add -A && git reset --hard
```
