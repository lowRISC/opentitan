# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for generating OTP images.

The rules in this file are used to generate a JSON file that describe the OTP
configuration which is then consumed to produce the OTP VMEM image file for
preloading the OTP in FPGA synthesis or simulation.
"""

def get_otp_images():
    """Returns a list of (otp_name, img_target) tuples.

    Each tuple corresponds to an OTP image defined in //hw/ip/otp_ctrl/data. The
    otp_name is a short, unique suffix of the image target, e.g. "rma". The
    img_target is the full path of the OTP image target.
    """

    img_targets = [
        "//hw/ip/otp_ctrl/data:img_dev",
        "//hw/ip/otp_ctrl/data:img_rma",
        "//hw/ip/otp_ctrl/data:img_test_unlocked0",
        "//hw/ip/otp_ctrl/data:img_prod",
        "//hw/ip/otp_ctrl/data:img_exec_disabled",
    ]

    out = []
    for img_target in img_targets:
        [_, img_target_name] = img_target.rsplit(":")
        otp_name = img_target_name.removeprefix("img_")
        out.append((
            otp_name,
            img_target,
        ))
    return out

def _otp_json_impl(ctx):
    """Bazel rule for generating JSON specifications for OTP configurations."""

    otp = {}

    # Seed to be used for generation of partition randomized values.
    # Can be overridden by the OTP image generation tool.
    otp["seed"] = "01931961561863975174"

    # Assemble all OTP paritions
    # The partition and item names must correspond with the OTP memory map.
    otp["partitions"] = [
        {
            "name": "CREATOR_SW_CFG",
            "items": {
                "CREATOR_SW_CFG_DIGEST": "0x0",
                # Use software mod_exp implementation for signature
                # verification. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_USE_SW_RSA_VERIFY": "0x739",
                # Mark the first two keys as valid and remaining as invalid
                # since we have currently only two keys. See the definition of
                # `hardened_byte_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_KEY_IS_VALID": "0x4b4b4b4b4b4ba5a5",
                # Enable use of entropy for countermeasures. See the definition
                # of `hardened_bool_t` in sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_RNG_EN": "0x739",
                # ROM execution is enabled if this item is set to a non-zero
                # value.
                "CREATOR_SW_CFG_ROM_EXEC_EN": ctx.attr.creator_sw_cfg_rom_exec_en,
                # Value to write to the cpuctrl CSR in `rom_init()`.
                # See:
                # https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#cpu-control-register-cpuctrl
                "CREATOR_SW_CFG_CPUCTRL": "0x1",
                "CREATOR_SW_CFG_JITTER_EN": "0x9",
                # Value of the min_security_version_rom_ext field of the
                # default boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT": "0x0",
                # Value of the min_security_version_bl0 field of the default
                # boot data.
                "CREATOR_SW_CFG_MIN_SEC_VER_BL0": "0x0",
                # Enable the default boot data in PROD and PROD_END life cycle
                # states. See the definition of `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": "0x739",
            },
        },
        {
            "name": "OWNER_SW_CFG",
            "items": {
                "OWNER_SW_CFG_DIGEST": "0x0",
                # Enable bootstrap. See `hardened_bool_t` in
                # sw/device/lib/base/hardened.h.
                "OWNER_SW_CFG_ROM_BOOTSTRAP_EN": "0x739",
                # Set to 0x739 to use the ROM_EXT hash measurement as the key
                # manager attestation binding value.
                "OWNER_SW_CFG_ROM_KEYMGR_ROM_EXT_MEAS_EN": "0x0",
                # Set the enables to kAlertEnableNone.
                # See `alert_enable_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASS_EN": "0xa9a9a9a9",
                # Set the esclation policies to kAlertEscalateNone.
                # See `alert_escalate_t`
                # in sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_ESCALATION": "0xd1d1d1d1",
                # Set the classifiactions to kAlertClassX.
                # See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION": ["0x94949494"] * 80,
                # Set the classifiactions to kAlertClassX.
                # See `alert_class_t` in
                # sw/device/silicon_creator/lib/drivers/alert.h
                "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION": ["0x94949494"] * 16,
                # Set the alert accumulation thresholds to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH": ["0x00000000"] * 4,
                # Set the alert timeout cycles to 0 per class.
                "OWNER_SW_CFG_ROM_ALERT_TIMEOUT_CYCLES": ["0x00000000"] * 4,
                # Set the alert phase cycles to 0,10,10,0xFFFFFFFF for classes
                # A and B, and to all zeros for classes C and D.
                "OWNER_SW_CFG_ROM_ALERT_PHASE_CYCLES": [
                    "0x0",
                    "0xa",
                    "0xa",
                    "0xFFFFFFFF",
                    "0x0",
                    "0xa",
                    "0xa",
                    "0xFFFFFFFF",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                    "0x0",
                ],
                "OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA": "0x36ed9cb0",
            },
        },
        {
            "name": "HW_CFG",
            # If set to true, this computes the HW digest value and locks the
            # partition.
            "lock": True,
            "items": {
                "DEVICE_ID": "<random>",
                # Cryptolib and chip-level tests require access to the CSRNG
                # software interfaces.
                "EN_CSRNG_SW_APP_READ": True,
                # Cryptolib and chip-level tests require access to the
                # entropy_src FW data interface.
                "EN_ENTROPY_SRC_FW_READ": True,
                # Cryptolib and chip-level tests require access to the
                # entropy_src FW override interface.
                "EN_ENTROPY_SRC_FW_OVER": True,
            },
        },
        {
            "name": "SECRET0",
            "lock": True,
            "items": {
                "TEST_UNLOCK_TOKEN": "<random>",
                "TEST_EXIT_TOKEN": "<random>",
            },
        },
        {
            "name": "SECRET1",
            "lock": True,
            "items": {
                "FLASH_ADDR_KEY_SEED": "<random>",
                "FLASH_DATA_KEY_SEED": "<random>",
                "SRAM_DATA_KEY_SEED": "<random>",
            },
        },
        {
            "name": "SECRET2",
            "lock": False,
            "items": {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
        },
        {
            "name": "LIFE_CYCLE",
            "state": ctx.attr.lc_state,
            # Can range from 0 to 16.
            # Note that a value of 0 is only permissible in RAW state.
            "count": ctx.attr.lc_count,
        },
    ]

    # For every partition with an "items" dictionary, expand the dictionary of
    # key:value pairs into a list of dicts, each of the form
    # {
    #   "name": key,
    #   "value": value
    # }
    # This format is expected by the OTP image generation tool
    for partition in otp["partitions"]:
        if "items" in partition.keys():
            items = partition["items"]
            partition["items"] = [{"name": k, "value": items[k]} for k in items.keys()]

    file = ctx.actions.declare_file("{}.json".format(ctx.attr.name))
    ctx.actions.write(file, json.encode_indent(otp))
    return DefaultInfo(files = depset([file]))

otp_json = rule(
    implementation = _otp_json_impl,
    attrs = {
        # Valid life cycle states can be found in the life cycle state
        # definition file (default: hw/ip/lc_ctrl/data/lc_ctrl_state.hjson)
        "lc_state": attr.string(doc = "Life cycle state", default = "RMA"),
        "lc_count": attr.int(doc = "Life cycle count", default = 8),
        "creator_sw_cfg_rom_exec_en": attr.string(default = "0xffffffff"),
    },
)

def _otp_image(ctx):
    output = ctx.actions.declare_file(ctx.attr.name + ".24.vmem")
    args = ctx.actions.args()
    args.add("--quiet")
    args.add("--lc-state-def", ctx.file.lc_state_def)
    args.add("--mmap-def", ctx.file.mmap_def)
    args.add("--img-cfg", ctx.file.src)
    args.add("--out", "{}/{}.BITWIDTH.vmem".format(output.dirname, ctx.attr.name))
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.src,
            ctx.file.lc_state_def,
            ctx.file.mmap_def,
        ],
        arguments = [args],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(files = depset([output]), runfiles = ctx.runfiles(files = [output]))]

otp_image = rule(
    implementation = _otp_image,
    attrs = {
        "src": attr.label(allow_single_file = True),
        "lc_state_def": attr.label(
            allow_single_file = True,
            default = "//hw/ip/lc_ctrl/data:lc_ctrl_state.hjson",
            doc = "Life-cycle state definition file in Hjson format.",
        ),
        "mmap_def": attr.label(
            allow_single_file = True,
            default = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
            doc = "OTP Controller memory map file in Hjson format.",
        ),
        "_tool": attr.label(
            default = "//util/design:gen-otp-img",
            executable = True,
            cfg = "exec",
        ),
    },
)
