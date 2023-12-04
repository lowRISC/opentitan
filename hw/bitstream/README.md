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

## Overriding Defaults in `opentitan_test` Targets

### Implicit Override Using Universal Bitstream Support (Recommended)

The `opentitan_test` rule supports the ability to customize the default
bitstream with a custom `otp` or `rom` image. The following example shows
how to inject an `otp` image to a test target.

```python
opentitan_test(
    name = "individualize_sw_cfg_functest",
    srcs = ["individualize_sw_cfg_functest.c"],
    cw310 = cw310_params(
        otp = "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival_bringup:otp_img_test_unlocked0_manuf_initialized",
        tags = ["manuf"],
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    },
    deps = [
        ":individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
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

> Bazel is configured to cache all bitstream splice operations triggered by
`otp` and/or `rom` dependencies in `opentitan_test` rules. For this reason, it
is recommended to use this approach over the use of the `bitstream_splice`
rule.

### Override by Using the `bitstream` Argument

> Only use this approach if you have to override the baseline `bitstream`
configuration for a given execution environment. In most cases, it is better
to use the `otp` and/or `rom` dependencies to customize the bitstream. See
the previous section for more details.

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
        ":individualize_sw_cfg_earlgrey_a0_sku_sival_bringup",
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

## Read More

* [OTP Build and Test Infrastructure](../ip/otp_ctrl/data/README.md)
