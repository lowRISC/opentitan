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
        "//hw/ip/otp_ctrl/data:img_prod_end",
        "//hw/ip/otp_ctrl/data:img_exec_disabled",
        "//hw/ip/otp_ctrl/data:img_bootstrap_disabled",
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
            partition["items"] = [{"name": k, "value": items[k]} for k in items.keys()]

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
    args.add_all(("otp", "alert-digest", ctx.file.otp_img))
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
    if ctx.attr.otp_seed:
        args.add("--otp-seed", ctx.attr.otp_seed[BuildSettingInfo].value)
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
        "otp_seed": attr.label(
            default = "//hw/ip/otp_ctrl/data:otp_seed",
            doc = "Configuration override seed used to randomize OTP netlist constants.",
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
