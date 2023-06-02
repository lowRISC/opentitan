# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")

PreSigningBinary = provider(fields = ["files"])

def _offline_presigning_artifacts(ctx):
    digests = []
    bins = []
    for src in ctx.files.srcs:
        pre = ctx.actions.declare_file(paths.replace_extension(src.basename, ".pre-signing"))
        bins.append(pre)
        ctx.actions.run(
            outputs = [pre],
            inputs = [src, ctx.file.manifest, ctx.file.key_file, ctx.executable._tool],
            arguments = [
                "--rcfile=",
                "image",
                "manifest",
                "update",
                "--manifest={}".format(ctx.file.manifest.path),
                "--rsa-key={}".format(ctx.file.key_file.path),
                "--output={}".format(pre.path),
                src.path,
            ],
            executable = ctx.executable._tool,
        )

        out = ctx.actions.declare_file(paths.replace_extension(src.basename, ".digest"))
        digests.append(out)
        ctx.actions.run(
            outputs = [out],
            inputs = [pre, ctx.executable._tool],
            arguments = [
                "--rcfile=",
                "image",
                "digest",
                "--bin={}".format(out.path),
                pre.path,
            ],
            executable = ctx.executable._tool,
        )
    return [
        DefaultInfo(files = depset(digests), data_runfiles = ctx.runfiles(files = digests)),
        PreSigningBinary(files = depset(bins)),
        OutputGroupInfo(digest = depset(digests), binary = depset(bins)),
    ]

offline_presigning_artifacts = rule(
    implementation = _offline_presigning_artifacts,
    attrs = {
        "srcs": attr.label_list(allow_files = True, doc = "Binary files to generate digests for"),
        "manifest": attr.label(allow_single_file = True, doc = "Manifest for this image"),
        "key_file": attr.label(allow_single_file = True, doc = "Public key to validate this image"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _strip_all_extensions(path):
    path = path.split(".")[0]
    return path

def _offline_fake_sign(ctx):
    outputs = []
    for file in ctx.files.srcs:
        out = ctx.actions.declare_file(paths.replace_extension(file.basename, ".sig"))
        ctx.actions.run(
            outputs = [out],
            inputs = [file, ctx.file.key_file],
            arguments = [
                "--rcfile=",
                "rsa",
                "sign",
                "--input={}".format(file.path),
                "--output={}".format(out.path),
                ctx.file.key_file.path,
            ],
            executable = ctx.executable._tool,
        )
        outputs.append(out)
    return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

offline_fake_sign = rule(
    implementation = _offline_fake_sign,
    attrs = {
        "srcs": attr.label_list(allow_files = True, doc = "Digest files to sign"),
        "key_file": attr.label(allow_single_file = True, doc = "Public key to validate this image"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
    doc = "Create detached signatures using on-disk private keys via opentitantool.",
)

def _offline_signature_attach(ctx):
    inputs = {}
    for src in ctx.attr.srcs:
        if PreSigningBinary in src:
            for file in src[PreSigningBinary].files.to_list():
                f = _strip_all_extensions(file.basename)
                inputs[f] = {"bin": file}
        elif DefaultInfo in src:
            for file in src[DefaultInfo].files.to_list():
                f = _strip_all_extensions(file.basename)
                inputs[f] = {"bin": file}
    for sig in ctx.files.signatures:
        f = _strip_all_extensions(sig.basename)
        if f not in inputs:
            fail("Signature {} does not have a corresponding entry in srcs".format(sig))
        inputs[f]["sig"] = sig

    outputs = []
    for f in inputs:
        if inputs[f].get("bin") == None:
            print("WARNING: No pre-signed binary for", f)
            continue
        if inputs[f].get("sig") == None:
            print("WARNING: No signature file for", f)
            continue
        out = ctx.actions.declare_file(paths.replace_extension(f, ".signed.bin"))
        ctx.actions.run(
            outputs = [out],
            inputs = [inputs[f]["bin"], inputs[f]["sig"], ctx.executable._tool],
            arguments = [
                "--rcfile=",
                "image",
                "manifest",
                "update",
                "--rsa-signature={}".format(inputs[f]["sig"].path),
                "--output={}".format(out.path),
                inputs[f]["bin"].path,
            ],
            executable = ctx.executable._tool,
        )
        outputs.append(out)
    return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

offline_signature_attach = rule(
    implementation = _offline_signature_attach,
    attrs = {
        "srcs": attr.label_list(allow_files = True, providers = [PreSigningBinary], doc = "Binary files to sign"),
        "signatures": attr.label_list(allow_files = True, doc = "Signed digest files"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)
