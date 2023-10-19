# FPGA Bitstreams

## Overview

The build infrastructure supports the ability to override the ROM and OTP
default values in precompiled FPGA bitstreams. The following configurations
are available for use in FPGA based test programs:

1. `rom_with_<key_type>_keys_<life_cycle_state>`
2. `test_rom`

`key_type` valid values are `real` or `fake`, with `fake` representing keys
that are part of the code base and can be used to sign objects. `fake` keys
are **not for production use cases**.

`life_cycle_state` maps to any of the life cycle states supported by the
OpenTitan design.

The following command shows a list of targets provided by `//hw/bitstream`:

```
bazel query //hw/bitstream:*
```

## Overriding Defaults in FPGA test cases

`opentitan_test` rules support the ability to override the `bitstream` used
in the test. To do this, simply set the `bitstream` argument to the bitstream
target.

The following example is taken from `sw/device/silicon_creator/manuf/lib/BUILD`:

```python
opentitan_test(
    name = "individualize_sw_cfg_functest",
    srcs = ["individualize_sw_cfg_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_test_unlocked0",
        tags = ["manuf"],
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        ":individualize_sw_cfg_earlgrey_a0_sku_generic",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
```

## Creating custom images for test cases

### Splicing the OTP memory

The `bitstream_slice` rule can be used to generate custom images. The following
example shows how to integrate a custom OTP image into a bitstream using the
`test_rom` image configuration.

```python
# Create a custom OTP JSON with flash scrambling and ECC enabled in the
# CREATOR_SW_CFG OTP partition.
otp_json(
    name = "power_virus_systemtest_otp_overlay",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                # Enable flash scrambling and ECC.
                "CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG": "0000090606",
            },
        ),
    ],
)

# Integrate the custom OTP JSON into an OTP image based on the `RMA` baseline
# configuration. The result will be an OTP configuration reflecting RMA
# life cycle state with flash scrambling and ECC enabled.
otp_image(
    name = "power_virus_systemtest_otp_img_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [":power_virus_systemtest_otp_overlay"],
    visibility = ["//visibility:private"],
)

# Generate an FPGA bitstream using `//hw/bitstream:test_rom` as the baseline
# bitstream, and splicing the OTP image provided by the target above.
bitstream_splice(
    name = "power_virus_systemtest_bitstream",
    src = "//hw/bitstream:test_rom",
    data = ":power_virus_systemtest_otp_img_rma",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)
```

### Splicing the ROM memory

The splicing mechanism can also be used to override the ROM in a bitstream by:

1. Setting `meminfo = //hw/bitstream:rom_mmi`; and,
2. Pointing the `data` attribute to a binary compiled against the ROM memory
   layout. For example:
   `data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem"`.

The following example shows how to splice a bitstream with the `test_rom`
binary.

```python
bitstream_splice(
    name = "test_rom",
    testonly = True,
    src = ":bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
)
```

## Read More

* [OTP Build and Test Infrastructure](../ip/otp_ctrl/data/README.md)
