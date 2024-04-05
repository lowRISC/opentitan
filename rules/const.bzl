# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:structs.bzl", "structs")

CONST = struct(
    # Must match the definitions in hardened.h.
    HARDENED_TRUE = 0x739,
    HARDENED_FALSE = 0x1d4,
    HARDENED_BYTE_TRUE = 0xa5,
    HARDENED_BYTE_FALSE = 0x4b,
    # Must match the definitions in sw/device/lib/base/multibits.h
    MUBI4_TRUE = 0x6,
    MUBI4_FALSE = 0x9,
    # Must match the definitions in chip.h.
    ROM_EXT = 0x4552544f,
    OWNER = 0x3042544f,
    MANIFEST_SIZE = 1024,
    ROM_EXT_SIZE_MIN = 1024,
    ROM_EXT_SIZE_MAX = 0x10000,
    BL0_SIZE_MIN = 1024,
    BL0_SIZE_MAX = 0x70000,
    DEFAULT_USAGE_CONSTRAINTS = 0xa5a5a5a5,
    # Must match the definition in spx_verify.h
    SPX_DISABLED = 0x8d6c8c17,
    SPX_SUCCESS = 0x8d6c8c17,
    # Must match the definitions in lc_ctrl_regs.h.
    LCV = struct(
        TEST_UNLOCKED0 = 0x02108421,
        TEST_LOCKED0 = 0x4210842,
        TEST_UNLOCKED1 = 0x6318c63,
        TEST_LOCKED1 = 0x8421084,
        TEST_UNLOCKED2 = 0xa5294a5,
        TEST_LOCKED2 = 0xc6318c6,
        TEST_UNLOCKED3 = 0xe739ce7,
        TEST_LOCKED3 = 0x10842108,
        TEST_UNLOCKED4 = 0x1294a529,
        TEST_LOCKED4 = 0x14a5294a,
        TEST_UNLOCKED5 = 0x16b5ad6b,
        TEST_LOCKED5 = 0x18c6318c,
        TEST_UNLOCKED6 = 0x1ad6b5ad,
        TEST_LOCKED6 = 0x1ce739ce,
        TEST_UNLOCKED7 = 0x1ef7bdef,
        DEV = 0x21084210,
        PROD = 0x2318c631,
        PROD_END = 0x25294a52,
        RMA = 0x2739ce73,
    ),
    # LC values used in software. Must match the definitions in lifecycle.h
    LCV_SW = struct(
        TEST = 0xb2865fbb,
        DEV = 0x0b5a75e0,
        PROD = 0x65f2520f,
        PROD_END = 0x91b9b68a,
        RMA = 0xcf8cfaab,
    ),
    # Must match the definitions in error.h.
    BFV = struct(
        INTERRUPT = struct(
            INSTRUCTION_ACCESS = 0x01495202,
            ILLEGAL_INSTRUCTION = 0x02495202,
            STORE_ACCESS = 0x07495202,
        ),
        SIGVERIFY = struct(
            BAD_RSA_SIGNATURE = 0x01535603,
            BAD_RSA_KEY = 0x04535603,
        ),
        BOOT_POLICY = struct(
            BAD_IDENTIFIER = 0x0142500d,
            BAD_LENGTH = 0x0242500d,
            ROLLBACK = 0x0342500d,
        ),
        MANIFEST = struct(
            BAD_ENTRY_POINT = 0x014d410d,
            BAD_CODE_REGION = 0x024d410d,
        ),
        BOOT_DATA = struct(
            NOT_FOUND = 0x0142440d,
            WRITE_CHECK = 0x0242440d,
            DATA_INVALID = 0x0342440d,
        ),
        UNKNOWN = 0xffffffff,
        OK = 0x739,
    ),
    # Must match the definitions in shutdown.h.
    SHUTDOWN = struct(
        PREFIX = struct(
            LCV = "LCV:",
            BFV = "BFV:",
        ),
        REDACT = struct(
            NONE = 0xe2290aa5,
            ERROR = 0x3367d3d4,
            MODULE = 0x1e791123,
            ALL = 0x48eb4bd9,
        ),
    ),
    # Must match the definitions in alert.h.
    ALERT = struct(
        NONE = 0xa9,
        ENABLE = 0x07,
        ENABLE_LOCKED = 0xd2,
        CLASS_X = 0x94,
        CLASS_A = 0xee,
        CLASS_B = 0x64,
        CLASS_C = 0xa7,
        CLASS_D = 0x32,
        ESC_NONE = 0xd1,
        ESC_PHASE_0 = 0xb9,
        ESC_PHASE_1 = 0xcb,
        ESC_PHASE_2 = 0x25,
        ESC_PHASE_3 = 0x76,
    ),
    MANUF_STATE = struct(
        SIVAL = 0x30305653,  # ASCII `SV00`.
        PRODC = 0x30304350,  # ASCII `PC00`.
        PRODA = 0x30304150,  # ASCII `PA00`.
    ),
)

_DEFAULT_LC_STATES = [
    CONST.LCV.TEST_UNLOCKED0,
    CONST.LCV.DEV,
    CONST.LCV.PROD,
    CONST.LCV.PROD_END,
    CONST.LCV.RMA,
]

def get_lc_items(*want_lc_values):
    """Return a list of key-value pairs from CONST.LCV with lowercased keys.

    If `want_lc_values` is empty, return the default dict. Otherwise, only
    key-value pairs where the value is in `want_lc_values` are returned.
    """
    lcv_dict = structs.to_dict(CONST.LCV)
    if not want_lc_values:
        want_lc_values = _DEFAULT_LC_STATES
    out = [(k.lower(), v) for k, v in lcv_dict.items() if v in want_lc_values]
    if len(out) != len(want_lc_values):
        fail("get_lc_items would produce list with incorrect length")
    return out

def lcv_hw_to_sw(hw_lc_state_val):
    """Return the software LCV corresponding to the given hardware LCV."""
    lcv_map = {
        CONST.LCV.DEV: CONST.LCV_SW.DEV,
        CONST.LCV.PROD: CONST.LCV_SW.PROD,
        CONST.LCV.PROD_END: CONST.LCV_SW.PROD_END,
        CONST.LCV.RMA: CONST.LCV_SW.RMA,
        CONST.LCV.TEST_UNLOCKED0: CONST.LCV_SW.TEST,
    }
    sw_lcv = lcv_map.get(hw_lc_state_val)
    if sw_lcv == None:
        fail("Could not find software LCV for hardware LCV: {}".format(hex(hw_lc_state_val)))
    return sw_lcv

_HEX_MAP = "0123456789abcdef"

def hex_digits(v, width = 32):
    """Convert an int into a hex string without 0x prefix"""
    if v >= (1 << width):
        fail("Int {} too large to convert to string of width {}".format(v, width))
    hex_digits = [_HEX_MAP[(v >> i) & 0xf] for i in range(0, width, 4)]
    return "".join(reversed(hex_digits))

def hex(v, width = 32):
    """Convert an int into a hex string with 0x prefix"""
    return "0x{}".format(hex_digits(v, width = width))

_REDACTION_MAP = {
    CONST.SHUTDOWN.REDACT.NONE: 0xffffffff,
    CONST.SHUTDOWN.REDACT.ERROR: 0x00ffffff,
    CONST.SHUTDOWN.REDACT.MODULE: 0x000000ff,
}

_REDACTION_LC_STATES = [CONST.LCV.DEV, CONST.LCV.PROD, CONST.LCV.PROD_END]

def error_redact(error, lc_state, redact):
    if lc_state not in _REDACTION_LC_STATES:
        return error
    if redact == CONST.SHUTDOWN.REDACT.ALL or redact not in _REDACTION_MAP:
        return CONST.BFV.UNKNOWN
    return error & _REDACTION_MAP.get(redact)

# Must match with top_earlgrey_alert_id in hw/top_earlgrey/sw/autogen/top_earlgrey.h
# The order of this list must match the order of the alerts in the OTP. Do not
# use a set here.
EARLGREY_ALERTS = [
    "uart0_fatal_fault",
    "uart1_fatal_fault",
    "uart2_fatal_fault",
    "uart3_fatal_fault",
    "gpio_fatal_fault",
    "spi_device_fatal_fault",
    "i2c0_fatal_fault",
    "i2c1_fatal_fault",
    "i2c2_fatal_fault",
    "pattgen_fatal_fault",
    "rv_timer_fatal_fault",
    "otp_ctrl_fatal_macro_error",
    "otp_ctrl_fatal_check_error",
    "otp_ctrl_fatal_bus_integ_error",
    "otp_ctrl_fatal_prim_otp_alert",
    "otp_ctrl_recov_prim_otp_alert",
    "lc_ctrl_fatal_prog_error",
    "lc_ctrl_fatal_state_error",
    "lc_ctrl_fatal_bus_integ_error",
    "spi_host0_fatal_fault",
    "spi_host1_fatal_fault",
    "usbdev_fatal_fault",
    "pwrmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_fault",
    "rstmgr_aon_fatal_cnsty_fault",
    "clkmgr_aon_recov_fault",
    "clkmgr_aon_fatal_fault",
    "sysrst_ctrl_aon_fatal_fault",
    "adc_ctrl_aon_fatal_fault",
    "pwm_aon_fatal_fault",
    "pinmux_aon_fatal_fault",
    "aon_timer_aon_fatal_fault",
    "sensor_ctrl_recov_alert",
    "sensor_ctrl_fatal_alert",
    "sram_ctrl_ret_aon_fatal_error",
    "flash_ctrl_recov_err",
    "flash_ctrl_fatal_std_err",
    "flash_ctrl_fatal_err",
    "flash_ctrl_fatal_prim_flash_alert",
    "flash_ctrl_recov_prim_flash_alert",
    "rv_dm_fatal_fault",
    "rv_plic_fatal_fault",
    "aes_recov_ctrl_update_err",
    "aes_fatal_fault",
    "hmac_fatal_fault",
    "kmac_recov_operation_err",
    "kmac_fatal_fault_err",
    "otbn_fatal",
    "otbn_recov",
    "keymgr_recov_operation_err",
    "keymgr_fatal_fault_err",
    "csrng_recov_alert",
    "csrng_fatal_alert",
    "entropy_src_recov_alert",
    "entropy_src_fatal_alert",
    "edn0_recov_alert",
    "edn0_fatal_alert",
    "edn1_recov_alert",
    "edn1_fatal_alert",
    "sram_ctrl_main_fatal_error",
    "rom_ctrl_fatal",
    "rv_core_ibex_fatal_sw_err",
    "rv_core_ibex_recov_sw_err",
    "rv_core_ibex_fatal_hw_err",
    "rv_core_ibex_recov_hw_err",
    "dummy65",
    "dummy66",
    "dummy67",
    "dummy68",
    "dummy69",
    "dummy70",
    "dummy71",
    "dummy72",
    "dummy73",
    "dummy74",
    "dummy75",
    "dummy76",
    "dummy77",
    "dummy78",
    "dummy79",
]

# Must match with hw/top_earlgrey/ip_autogen/alert_handler/data/alert_handler.hjson
# The order of this list must match the order of the alerts in the OTP. Do not
# use a set here.
EARLGREY_LOC_ALERTS = [
    "alert_pingfail",
    "esc_pingfail",
    "alert_integfail",
    "esc_integfail",
    "bus_integfail",
    "shadow_reg_update_error",
    "shadow_reg_storage_error",
    "loc_dummy7",
    "loc_dummy8",
    "loc_dummy9",
    "loc_dummy10",
    "loc_dummy11",
    "loc_dummy12",
    "loc_dummy13",
    "loc_dummy14",
    "loc_dummy15",
]

KEY_AUTHENTICITY = [
    "fake",
    "real",
]
