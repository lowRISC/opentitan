# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules for generating OTP images.

OTP image generation begins with producing one or more (H)JSON files that
describe the OTP configuration. These files are then consumed by the OTP image
generation tool to produce the OTP VMEM image file used to preload the OTP in
FPGA synthesis or simulation.

The JSON file generation is handled by the otp_json rule, which accepts a list
of partitions. Due to Bazel's limited datatypes for rule attributes, a helper
function (otp_partition) is used to serialize the representation of each
partition to pass it into otp_json as a string.

Usage example:
otp_json(
    name = "example_otp_json",
    partitions = [
        otp_partition(
            name = "Partition0",
            lock = True,
            items = {
                "ITEM_1": "abc",
                "ITEM_2": "<random>",
            }
        ),
        otp_partition(...),
    ],
)

Note that the "items" dictionary for each partition should be expressed as
{"key": "value"} mappings. This will be expanded by the otp_json rule into a
list of dicts, each of the form {"name": key, "value": value}, which is the
format expected by the image generation tool.
"""

load("@bazel_skylib//rules:common_settings.bzl", "BuildSettingInfo")
load("@bazel_skylib//lib:new_sets.bzl", "sets")
load("//rules:host.bzl", "host_tools_transition")
load("//rules:const.bzl", "CONST", "hex")

def get_otp_images():
    """Returns a list of (otp_name, img_target) tuples.

    Each tuple corresponds to an OTP image defined in //hw/ip/otp_ctrl/data. The
    otp_name is a short, unique suffix of the image target, e.g. "rma". The
    img_target is the full path of the OTP image target.
    """

    img_targets = [
        "//hw/ip/otp_ctrl/data:img_dev",
        "//hw/ip/otp_ctrl/data:img_dev_individualized",
        "//hw/ip/otp_ctrl/data:img_rma",
        "//hw/ip/otp_ctrl/data:img_test_locked0",
        "//hw/ip/otp_ctrl/data:img_test_locked1",
        "//hw/ip/otp_ctrl/data:img_test_locked2",
        "//hw/ip/otp_ctrl/data:img_test_locked3",
        "//hw/ip/otp_ctrl/data:img_test_locked4",
        "//hw/ip/otp_ctrl/data:img_test_locked5",
        "//hw/ip/otp_ctrl/data:img_test_locked6",
        "//hw/ip/otp_ctrl/data:img_test_unlocked0",
        "//hw/ip/otp_ctrl/data:img_test_unlocked1",
        "//hw/ip/otp_ctrl/data:img_test_unlocked1_initial",
        "//hw/ip/otp_ctrl/data:img_test_unlocked2",
        "//hw/ip/otp_ctrl/data:img_test_unlocked3",
        "//hw/ip/otp_ctrl/data:img_test_unlocked4",
        "//hw/ip/otp_ctrl/data:img_test_unlocked5",
        "//hw/ip/otp_ctrl/data:img_test_unlocked6",
        "//hw/ip/otp_ctrl/data:img_test_unlocked7",
        "//hw/ip/otp_ctrl/data:img_prod",
        "//hw/ip/otp_ctrl/data:img_prod_end",
        "//hw/ip/otp_ctrl/data:img_exec_disabled",
        "//hw/ip/otp_ctrl/data:img_bootstrap_disabled",
        "//hw/ip/otp_ctrl/data:img_raw",
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

def otp_partition(name, **kwargs):
    partition = {
        "name": name,
    }
    partition.update(kwargs)
    return json.encode(partition)

def _otp_json_impl(ctx):
    otp = {}
    if ctx.attr.seed != "":
        otp["seed"] = ctx.attr.seed
    otp["partitions"] = [json.decode(p) for p in ctx.attr.partitions]

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
            partition["items"] = [{"name": k, "value": v} for k, v in items.items()]

    file = ctx.actions.declare_file("{}.json".format(ctx.attr.name))
    ctx.actions.write(file, json.encode_indent(otp))
    return [DefaultInfo(files = depset([file]))]

otp_json = rule(
    implementation = _otp_json_impl,
    attrs = {
        "seed": attr.string(
            doc = "Seed to be used for generation of partition randomized values. Can be overridden by the OTP image generation tool.",
        ),
        "partitions": attr.string_list(doc = "A list of serialized partitions from otp_partition."),
    },
)

def _otp_alert_digest_impl(ctx):
    file = ctx.actions.declare_file("{}.json".format(ctx.attr.name))

    outputs = [file]

    inputs = [
        ctx.file._opentitantool,
        ctx.file.otp_img,
    ]

    args = ctx.actions.args()
    args.add_all(("--rcfile=", "otp", "alert-digest", ctx.file.otp_img))
    args.add("--output", file)

    ctx.actions.run(
        outputs = outputs,
        inputs = inputs,
        arguments = [args],
        executable = ctx.file._opentitantool.path,
    )

    return [DefaultInfo(files = depset([file]))]

otp_alert_digest = rule(
    implementation = _otp_alert_digest_impl,
    attrs = {
        "otp_img": attr.label(
            allow_single_file = [".json", ".hjson"],
            doc = "The OTP image file containing alert_handler values.",
        ),
        "_opentitantool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            allow_single_file = True,
            executable = True,
            cfg = host_tools_transition,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def _otp_image(ctx):
    output = ctx.actions.declare_file(ctx.attr.name + ".24.vmem")
    args = ctx.actions.args()
    if not ctx.attr.verbose:
        args.add("--quiet")
    args.add("--lc-state-def", ctx.file.lc_state_def)
    args.add("--mmap-def", ctx.file.mmap_def)
    if ctx.attr.img_seed:
        args.add("--img-seed", ctx.attr.img_seed[BuildSettingInfo].value)
    if ctx.attr.lc_seed:
        args.add("--lc-seed", ctx.attr.lc_seed[BuildSettingInfo].value)
    if ctx.attr.otp_seed:
        args.add("--otp-seed", ctx.attr.otp_seed[BuildSettingInfo].value)
    if ctx.attr.data_perm:
        args.add("--data-perm", ctx.attr.data_perm[BuildSettingInfo].value)
    args.add("--img-cfg", ctx.file.src)
    args.add_all(ctx.files.overlays, before_each = "--add-cfg")
    args.add("--out", "{}/{}.BITWIDTH.vmem".format(output.dirname, ctx.attr.name))
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.src,
            ctx.file.lc_state_def,
            ctx.file.mmap_def,
        ] + ctx.files.overlays,
        arguments = [args],
        executable = ctx.executable._tool,
    )
    return [DefaultInfo(files = depset([output]), runfiles = ctx.runfiles(files = [output]))]

otp_image = rule(
    implementation = _otp_image,
    attrs = {
        "src": attr.label(
            allow_single_file = [".json", ".hjson"],
            doc = "Image configuration file in Hjson format.",
        ),
        "overlays": attr.label_list(
            allow_files = [".json", ".hjson"],
            doc = "Additional image configuration file(s) in Hjson format to override src. Overlays are applied in the order provided.",
        ),
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
        "img_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:img_seed",
            doc = "Configuration override seed used to randomize field values in an OTP image.",
        ),
        "lc_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:lc_seed",
            doc = "Configuration override seed used to randomize LC netlist constants.",
        ),
        "otp_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:otp_seed",
            doc = "Configuration override seed used to randomize OTP netlist constants.",
        ),
        "data_perm": attr.label(
            default = "//hw/ip/otp_ctrl/data:data_perm",
            doc = "Post-processing option to trigger permuting bit positions in memfile.",
        ),
        "verbose": attr.bool(
            default = False,
            doc = "Display progress messages from image-generation tool.",
        ),
        "_tool": attr.label(
            default = "//util/design:gen-otp-img",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _otp_image_consts_impl(ctx):
    output = ctx.actions.declare_file(ctx.attr.name + ".c")
    args = ctx.actions.args()
    if not ctx.attr.verbose:
        args.add("--quiet")
    args.add("--lc-state-def", ctx.file.lc_state_def)
    args.add("--mmap-def", ctx.file.mmap_def)
    args.add("--img-seed", ctx.attr.img_seed[BuildSettingInfo].value)
    args.add("--lc-seed", ctx.attr.lc_seed[BuildSettingInfo].value)
    args.add("--otp-seed", ctx.attr.otp_seed[BuildSettingInfo].value)
    args.add("--img-cfg", ctx.file.src)
    args.add("--c-template", ctx.file.c_template)
    args.add("--c-out", "{}/{}.c".format(output.dirname, ctx.attr.name))
    args.add_all(ctx.files.overlays, before_each = "--add-cfg")
    ctx.actions.run(
        outputs = [output],
        inputs = [
            ctx.file.src,
            ctx.file.c_template,
            ctx.file.lc_state_def,
            ctx.file.mmap_def,
        ] + ctx.files.overlays,
        arguments = [args],
        executable = ctx.executable._tool,
    )
    return [
        DefaultInfo(files = depset([output]), runfiles = ctx.runfiles(files = [output])),
    ]

otp_image_consts = rule(
    implementation = _otp_image_consts_impl,
    attrs = {
        "src": attr.label(
            allow_single_file = [".json", ".hjson"],
            doc = "Image configuration file in Hjson format.",
        ),
        "overlays": attr.label_list(
            allow_files = [".json", ".hjson"],
            doc = "Additional image configuration file(s) in Hjson format to override src. Overlays are applied in the order provided.",
        ),
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
        "img_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:img_seed",
            doc = "Configuration override seed used to randomize field values in an OTP image.",
        ),
        "lc_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:lc_seed",
            doc = "Configuration override seed used to randomize LC netlist constants.",
        ),
        "otp_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:otp_seed",
            doc = "Configuration override seed used to randomize OTP netlist constants.",
        ),
        "c_template": attr.label(
            allow_single_file = True,
            default = "//hw/ip/otp_ctrl/data:otp_ctrl_img.c.tpl",
            doc = "OTP image header template.",
        ),
        "verbose": attr.bool(
            default = False,
            doc = "Display progress messages from image-generation tool.",
        ),
        "_tool": attr.label(
            default = "//util/design:gen-otp-img",
            executable = True,
            cfg = "exec",
        ),
    },
)

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
# This set overlays does not include any of the SECRET[0-2] partitions.
STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS = [
    "//hw/ip/otp_ctrl/data:otp_json_creator_sw_cfg",
    "//hw/ip/otp_ctrl/data:otp_json_owner_sw_cfg",
    "//hw/ip/otp_ctrl/data:otp_json_alert_digest_cfg",
    "//hw/ip/otp_ctrl/data:otp_json_hw_cfg",
]

# This is a set of overlays to generate a generic, standard OTP image.
# Additional overlays can be applied on top to further customize the OTP.
STD_OTP_OVERLAYS = STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS + [
    "//hw/ip/otp_ctrl/data:otp_json_secret0",
    "//hw/ip/otp_ctrl/data:otp_json_secret1",
    "//hw/ip/otp_ctrl/data:otp_json_secret2_unlocked",
]

def otp_hex(v):
    return hex(v)

def otp_bytestring(byte_list):
    val = 0
    for b in reversed(byte_list):
        if b >= (1 << 8):
            fail("All elements in the byte list must be <= 0xff")
        val = (val << 8) | b
    return hex(val, width = 8 * len(byte_list))

def _parse_str_list(s):
    """Parse a string with comma delimiters as a list of strings, ignoring spaces.

    This function is a workaround when lists need to be provided as arguments in
    a compact form in a BUILD file. Leaving the argument as a list causes
    buildifier to reformat it onto multiple lines whereas a string is kept as
    one line. This function can be removed once buildifier supports exempting
    regions from auto-formatting.

    Example:
    _parse_str_list("  a, b,    c, d") -> ["a", "b", "c", "d"]
    """
    return s.replace(" ", "").split(",")

def otp_alert_classification(alert_list, default = None, **kwargs):
    """Create an array specifying the alert classifications.

    This function creates an array of bytestrings that specifies the alert
    classification for each alert within each lifecycle state.

    Args:
        alert_list: list of all supported alerts in the order required by the
            OTP. Alert lists can be found in const.bzl.
        default: default classification for all alerts that are not specified
            in kwargs. If kwargs does not include all alerts, a value must be
            specified for default.
        kwargs: a mapping of the format 'alert_name = alert_class_string'.
            alert_name is an alert in the alert_list argument.
            alert_class_string is a comma-delimited string that can contain
            spaces and is intended to be parsed by the _parse_str_list macro.
            This string must indicate exactly 4 alert classes for the prod,
            prod_end, dev, and rma LC states in that order.

    Returns:
        Alert classification specification as a list of bytestrings.

    Example usage:
        otp_alert_classification(
            alert_list = EARLGREY_ALERTS,
            # The ordering is "prod, prod_end, dev, rma"
            default = "                   X, X, X, X",
            gpio_fatal_fault = "          X, X, X, X",
            i2c0_fatal_fault = "          X, X, X, X",
            otp_ctrl_fatal_macro_error = "X, X, X, X",
        ),
    """

    def _parse_alert_class_string(s):
        classes = _parse_str_list(s)
        if len(classes) != 4:
            fail("Exactly 4 classes must be specified (for prod, prod_end, dev, and rma LC states)")
        alert_class_bytes = [getattr(CONST.ALERT, "CLASS_{}".format(c)) for c in classes]
        return otp_bytestring(alert_class_bytes)

    provided_alerts = dict()
    for alert, class_str in kwargs.items():
        provided_alerts[alert] = _parse_alert_class_string(class_str)

    alert_set = sets.make(alert_list)
    provided_alert_set = sets.make(provided_alerts.keys())

    # Provided alerts must not have any unknown alerts
    unknown_alerts = sets.difference(provided_alert_set, alert_set)
    if sets.length(unknown_alerts) > 0:
        fail("Some provided alerts are not known by this macro: {}".format(unknown_alerts))

    # If a default is not provided, the provided alerts must match exactly with the alert_set
    if default == None:
        extra_alerts = sets.difference(alert_set, provided_alert_set)
        if sets.length(extra_alerts) > 0:
            fail("Some alerts were not specified and no default was provided: {}".format(extra_alerts))
    else:
        default = _parse_alert_class_string(default)

    return [provided_alerts.get(alert, default = default) for alert in alert_list]

def otp_per_class_bytes(A, B, C, D):
    """Create a bytestring of per-alert-class byte values."""
    return otp_bytestring([A, B, C, D])

def otp_per_class_ints(A, B, C, D):
    """Create a list of per-alert-class int values."""
    return [otp_hex(x) for x in (A, B, C, D)]

def otp_per_class_lists(A, B, C, D):
    """Create a list of per-alert-class parameters.

    Args:
        A, B, C, D: a comma-delimited string indicating the parameters for each
            alert class.

    Returns:
        The parameters of the provided lists are all joined together. This macro
        returns one list of strings.
    """
    cfg_list = list()
    for x in (A, B, C, D):
        cfg_list.extend([otp_hex(int(i, base = 16)) for i in _parse_str_list(x)])
    return cfg_list
