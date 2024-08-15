# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("@rules_rust//bindgen:bindgen.bzl", "rust_bindgen_library")

package(default_visibility = ["//visibility:public"])

# NOTE: This variable is modified during English breakfast SW build from prepare_sw.py.
_TOPLEVEL = "earlgrey"

_ENGLISH_BREAKFAST_DEPS = [
    "//sw/device/lib/dif:aon_timer",
    "//sw/device/lib/dif:clkmgr",
    "//sw/device/lib/dif:lc_ctrl",
    "//sw/device/lib/dif:otp_ctrl",
    "//sw/device/lib/dif:rstmgr",
    "//sw/device/lib/dif:uart",
]

_EARLGREY_DEPS = [
    "//sw/device/lib/dif:adc_ctrl",
    "//sw/device/lib/dif:aes",
    "//sw/device/lib/dif:alert_handler",
    "//sw/device/lib/dif:aon_timer",
    "//sw/device/lib/dif:clkmgr",
    "//sw/device/lib/dif:csrng",
    "//sw/device/lib/dif:edn",
    "//sw/device/lib/dif:entropy_src",
    "//sw/device/lib/dif:flash_ctrl",
    "//sw/device/lib/dif:gpio",
    "//sw/device/lib/dif:hmac",
    "//sw/device/lib/dif:i2c",
    "//sw/device/lib/dif:keymgr",
    "//sw/device/lib/dif:kmac",
    "//sw/device/lib/dif:lc_ctrl",
    "//sw/device/lib/dif:otbn",
    "//sw/device/lib/dif:otp_ctrl",
    "//sw/device/lib/dif:pattgen",
    "//sw/device/lib/dif:pinmux",
    "//sw/device/lib/dif:pwm",
    "//sw/device/lib/dif:pwrmgr",
    "//sw/device/lib/dif:rstmgr",
    "//sw/device/lib/dif:rv_timer",
    "//sw/device/lib/dif:sensor_ctrl",
    "//sw/device/lib/dif:spi_device",
    "//sw/device/lib/dif:spi_host",
    "//sw/device/lib/dif:sram_ctrl",
    "//sw/device/lib/dif:sysrst_ctrl",
    "//sw/device/lib/dif:uart",
    "//sw/device/lib/dif:usbdev",
]

_DEPS = _ENGLISH_BREAKFAST_DEPS if _TOPLEVEL == "englishbreakfast" else _EARLGREY_DEPS

cc_library(
    name = "difs",
    hdrs = ["difs.h"],
    deps = _DEPS,
)

rust_bindgen_library(
    name = "alert",
    bindgen_flags = [
        "--allowlist-type=AlertClass",
        "--allowlist-type=AlertEnable",
        "--allowlist-type=AlertEscalate",
    ],
    cc_lib = "//sw/device/silicon_creator/lib/drivers:alert",
    header = "//sw/device/silicon_creator/lib/drivers:alert.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
    ],
)

rust_bindgen_library(
    name = "dif",
    bindgen_flags = [
        "--allowlist-var=ADC_CTRL_.*_REG_OFFSET",
        "--allowlist-var=AES_.*_REG_OFFSET",
        "--allowlist-var=ALERT_HANDLER_.*_REG_OFFSET",
        "--allowlist-var=AON_TIMER_.*_OFFSET",
        "--allowlist-var=CLKMGR_.*_BIT",
        "--allowlist-var=CLKMGR_.*_REG_OFFSET",
        "--allowlist-var=CLKMGR_.*_MASK",
        "--allowlist-var=CLKMGR_.*_OFFSET",
        "--allowlist-var=CSRNG_.*_REG_OFFSET",
        "--allowlist-type=dif_lc_ctrl_state",
        "--allowlist-type=dif_lc_ctrl_token",
        "--allowlist-var=EDN_.*_REG_OFFSET",
        "--allowlist-var=ENTROPY_SRC_.*_REG_OFFSET",
        "--allowlist-var=FLASH_CTRL_.*_REG_OFFSET",
        "--allowlist-var=GPIO_.*_REG_OFFSET",
        "--allowlist-var=HMAC_.*_REG_OFFSET",
        "--allowlist-var=I2C_.*_REG_OFFSET",
        "--allowlist-var=KEYMGR_.*_REG_OFFSET",
        "--allowlist-var=KMAC_.*_REG_OFFSET",
        "--allowlist-var=LC_CTRL_.*_BIT",
        "--allowlist-var=LC_CTRL_.*_REG_OFFSET",
        "--allowlist-var=OTBN_.*_REG_OFFSET",
        "--allowlist-var=OTBN_.*_SIZE_BYTES",
        "--allowlist-var=OTP_CTRL_.*_BIT",
        "--allowlist-var=OTP_CTRL_.*_OFFSET",
        "--allowlist-var=OTP_CTRL_.*_SIZE",
        "--allowlist-var=PATTGEN_.*_REG_OFFSET",
        "--allowlist-var=PINMUX_.*_REG_OFFSET",
        "--allowlist-var=PWM_.*_REG_OFFSET",
        "--allowlist-var=PWRMGR_.*_REG_OFFSET",
        "--allowlist-type=dif_rstmgr_reset_info",
        "--allowlist-var=RSTMGR_.*_OFFSET",
        "--allowlist-var=RV_TIMER_.*_REG_OFFSET",
        "--allowlist-var=SENSOR_CTRL_.*_REG_OFFSET",
        "--allowlist-var=SPI_DEVICE_.*_REG_OFFSET",
        "--allowlist-var=SPI_HOST_.*_REG_OFFSET",
        "--allowlist-var=SRAM_CTRL_.*_REG_OFFSET",
        "--allowlist-var=SYSRST_CTRL_.*_REG_OFFSET",
        "--allowlist-var=UART_.*_OFFSET",
        "--allowlist-var=USBDEV_.*_REG_OFFSET",
    ],
    cc_lib = ":difs",
    clang_flags = [
        "-DOT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_",
    ] if _TOPLEVEL == "englishbreakfast" else [
    ],
    header = "difs.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "earlgrey",
    bindgen_flags = [
        "--allowlist-type=top_earlgrey_alert_peripheral",
        "--allowlist-type=top_earlgrey_alert_id",
        "--allowlist-type=top_earlgrey_pinmux_peripheral_in",
        "--allowlist-type=top_earlgrey_pinmux_insel",
        "--allowlist-type=top_earlgrey_pinmux_mio_out",
        "--allowlist-type=top_earlgrey_pinmux_outsel",
        "--allowlist-type=top_earlgrey_direct_pads",
        "--allowlist-type=top_earlgrey_muxed_pads",
        "--allowlist-type=top_earlgrey_power_manager_wake_ups",
        "--allowlist-type=top_earlgrey_reset_manager_sw_resets",
        "--allowlist-type=top_earlgrey_power_manager_reset_requests",
        "--allowlist-type=top_earlgrey_gateable_clocks",
        "--allowlist-type=top_earlgrey_hintable_clocks",
    ],
    cc_lib = "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    header = "//hw/top_earlgrey/sw/autogen:top_earlgrey.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "hardened",
    bindgen_flags = [
        "--allowlist-type=hardened_bool",
        "--allowlist-type=hardened_byte_bool",
    ],
    cc_lib = "//sw/device/lib/base:hardened",
    header = "//sw/device/lib/base:hardened.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "multibits",
    bindgen_flags = [
        "--allowlist-type=multi_bit_bool",
    ],
    cc_lib = "//sw/device/lib/base:multibits",
    header = "//sw/device/lib/base:multibits.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "sram_program",
    bindgen_flags = [
        "--allowlist-var=SRAM_MAGIC_SP_.*",
    ],
    cc_lib = "//sw/device/silicon_creator/manuf/lib:sram_start_headers",
    header = "//sw/device/silicon_creator/manuf/lib:sram_start.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "status",
    bindgen_flags = [
        "--allowlist-type=ot_status_create_record_t",
        "--allowlist-type=ot_status_create_record_magic",
        "--allowlist-type=status",
        "--allowlist-type=status_t",
        "--allowlist-type=absl_status_t",
        "--allowlist-function=status_create",
        "--allowlist-function=status_extract",
        # status_err and status_ok are marked as always inline but are also
        # declared as extern in status.c which means that will actually end up
        # in the object file.
        "--allowlist-function=status_err",
        "--allowlist-function=status_ok",
        "--generate-inline-functions",
        "--with-derive-custom=ot_status_create_record=zerocopy::FromZeroes",
        "--with-derive-custom=ot_status_create_record=zerocopy::FromBytes",
    ],
    cc_lib = "//sw/device/lib/base:status",
    header = "//sw/device/lib/base:status.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
    deps = [
        "@crate_index//:zerocopy",
    ],
)

rust_bindgen_library(
    name = "test_status",
    bindgen_flags = [
        "--allowlist-type=test_status_t",
    ],
    cc_lib = "//sw/device/lib/testing/test_framework:status_headers",
    header = "//sw/device/lib/testing/test_framework:status.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_bindgen_library(
    name = "perso_objects",
    bindgen_flags = [
        "--allowlist-type=perso_object_type_t",
        "--allowlist-type=object_header_t",
        "--allowlist-type=cert_header_t",
        "--allowlist-type=dev_seed_header_t",
        "--allowlist-type=obj_header_fields_t",
        "--allowlist-type=cert_header_fields_t",
    ],
    cc_lib = "//sw/device/silicon_creator/manuf/base:perso_object_headers",
    header = "//sw/device/silicon_creator/manuf/base:perso_tlv_data.h",
    rustc_flags = [
        "--allow=non_snake_case",
        "--allow=non_upper_case_globals",
        "--allow=non_camel_case_types",
    ],
)

rust_library(
    name = "bindgen",
    srcs = ["lib.rs"],
    deps = [
        ":alert",
        ":dif",
        ":earlgrey",
        ":hardened",
        ":multibits",
        ":perso_objects",
        ":sram_program",
        ":status",
        ":test_status",
    ],
)
