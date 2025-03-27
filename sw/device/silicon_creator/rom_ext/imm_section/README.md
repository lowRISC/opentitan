# RomExt Immutable Section Release Guide

## Bump the release version

Edit the `IMM_SECTION_VERSION_{MAJOR,MINOR}"` line in the bazel file.
`sw/device/silicon_creator/rom_ext/imm_section/defs.bzl`

After editing, the edit PR should be MERGED before continuing to create
reproducible builds from a clean tree in the mainline.

Building / stamping from a dirty tree should only be done for testing purposes.

## Build a release bundle

```shell
$ bazel build --stamp //sw/device/silicon_creator/rom_ext/imm_section:release_bundle
```

Building with --stamp flag will stamp the built immutable section, including
the commit hash and the workspace status.

Note: Building from a dirty tree or unmerged commit should only be done for
testing purposes. When building under dirty tree, the output folder will be
suffixed with "-modified" automatically.

The command will create a release tarball in
`bazel-bin/sw/device/silicon_creator/rom_ext/imm_section/release_bundle.tar`.

The built tarball contains:

*   a generated BUILD file that can be referenced by the ROM\_EXT target, and
*   compiled imm\_section binary for each variant, and
*   elf / map files corresponding to each binary for debugging purposes.

## Submit a prebuilt release

Extracting the tarball to your prebuilt folder will create the prebuilt targets
that can be linked to ROM\_EXT. The prebuilt folder should be checked-in to either:

*   this (upstream) repo under: `sw/device/silicon_creator/rom\_ext/imm_section/prebuilts/`, or
*   to a (downstream) integrators repo.

```shell
$ tar xvf \
  bazel-bin/sw/device/silicon_creator/rom_ext/imm_section/release_bundle.tar \
  -C sw/device/silicon_creator/rom_ext/imm_section/prebuilts/
2025-03-28-v0.1-d686b36b/BUILD
2025-03-28-v0.1-d686b36b/main_binaries_dice_x509_slot_virtual_silicon_creator.bin
2025-03-28-v0.1-d686b36b/main_binaries_dice_x509_slot_virtual_silicon_creator.elf
2025-03-28-v0.1-d686b36b/main_binaries_dice_x509_slot_virtual_silicon_creator.map
2025-03-28-v0.1-d686b36b/main_binaries_dice_cwt_slot_virtual_silicon_creator.bin
2025-03-28-v0.1-d686b36b/main_binaries_dice_cwt_slot_virtual_silicon_creator.elf
2025-03-28-v0.1-d686b36b/main_binaries_dice_cwt_slot_virtual_silicon_creator.map

$ ./bazelisk.sh query //sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b/...
//sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b:dice_cwt
//sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b:dice_cwt_object
//sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b:dice_x509
//sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b:dice_x509_object
```

## Create ROM\_EXT with a prebuilt release

The immutable section is linked to ROM\_EXT by deps. To build a ROM\_EXT with
prebuilt release, please update the deps to the corresponding variants listed
above. For example,

```diff
  deps = [
-     "@//sw/device/silicon_creator/rom_ext/imm_section:main_section_dice_cwt_slot_virtual",
+     "@//sw/device/silicon_creator/rom_ext/imm_section/prebuilts/2025-03-28-v0.1-d686b36b:dice_cwt",
  ]
```

## Enforce immutability hash check in OTP

The immutability check is disabled by default. Integrator needs to flip the
settings in their SKU's OTP image to enforce the hash of the immutable section.

For example, include the following overlay to the perso OTP images.

```python
otp_json_immutable_rom_ext(
    name = "otp_json_imm_rom_ext_hash",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items =
                {
                    "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(CONST.HARDENED_TRUE),
                },
        ),
    ],
    rom_ext = "//path/to/your:rom_ext_target",
    visibility = ["//visibility:private"],
)
```
