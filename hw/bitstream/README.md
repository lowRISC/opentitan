# FPGA Bitstreams

## Overview

The build infrastructure allows you to build a "base" bitstream for FPGA targets.
The ROM and OTP can then be overridden by programming the FPGA via the dedicated `bkdr_loader` IP.
This can be done over JTAG using `opentitantool`.

Different combinations of ROM, OTP and other settings are defined in execution environments.
These are then automatically applied when running a test using that execution environment.
The following command shows a list of FPGA environments supported for the Earl Grey top, for example:

```
bazel query "filter('//hw/top_earlgrey:fpga_', //hw/top_earlgrey/...)"
```

In general, there are two ROM images that are used:

1. The mask ROM (`//sw/device/silicon_creator/rom:mask_rom`)
2. The test ROM (`//sw/device/lib/testing/test_rom:test_rom`)

Execution environments might have different key definitions, where keys can be `real` or `fake`.
Keys that are `fake` are part of the code base and can be used to sign objects, and are **not for production use cases**.

OTP images can be used to customize a variety of different configuration options.
Importantly, they can be used to define the life cycle state that OpenTitan is in.
Various OTP images are available under the relevant top-level's data files, and custom configurations can be added via relevant Bazel rules.
The available OTP images for Earl Grey can be queried with the following command:

```
bazel query "kind('otp_image', //hw/top_earlgrey/data/otp/...)"
```

## Overriding Defaults in `opentitan_test` Targets

### Implicit Override Using Universal Bitstream Support (Recommended)

The `opentitan_test` rule supports the ability to customize the default bitstream with a custom `otp` or `rom` image.
The following example shows how to inject an `otp` image to a test target.

```python
opentitan_test(
    name = "individualize_sw_cfg_functest",
    srcs = ["individualize_sw_cfg_functest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    fpga = fpga_params(
        # If the test changes the stored OTP values during execution, it should use this flag
        changes_otp = True,
        # Customize the OTP image
        otp = "//hw/top_earlgrey/data/otp:img_test_unlocked1",
        tags = ["manuf"],
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/manuf/individualize_sw_cfg_functest",
    ),
    deps = [
        ":flash_info_fields",
        ":individualize_sw_cfg_em00",
        "//hw/top:otp_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
        "//sw/device/lib/testing:rstmgr_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)
```

### Override by Using the `bitstream` Argument

> Only use this approach if you have to override the baseline `bitstream` configuration for a given execution environment.
> **In almost all cases, it is better to use the `otp` and/or `rom` dependencies to customize the bitstream.**
> See the previous section for more details.

`opentitan_test` rules support the ability to override the `bitstream` used in the test.
To do this, simply set the `bitstream` argument to the bitstream target.

```python
opentitan_test(
    name = "individualize_sw_cfg_functest",
    srcs = ["individualize_sw_cfg_functest.c"],
    fpga = fpga_params(
        bitstream = "//hw/bitstream:custom_bitstream_target",
        tags = ["manuf"],
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    },
    deps = [
        ":individualize_sw_cfg_earlgrey_sku_sival",
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

* [OTP Preload Image Generator](../../util/design/README.md#otp_preload_image_generator)
