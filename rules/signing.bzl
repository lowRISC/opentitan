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
        inputs = [
            src,
            ctx.file.manifest,
            ctx.file.rsa_key,
            ctx.executable._tool,
        ]
        spx_args = []
        if ctx.file.spx_key:
            spx_args.append("--spx-key={}".format(ctx.file.spx_key.path))
            inputs.append(ctx.file.spx_key)
        ctx.actions.run(
            outputs = [pre],
            inputs = inputs,
            arguments = [
                "--rcfile=",
                "image",
                "manifest",
                "update",
                "--manifest={}".format(ctx.file.manifest.path),
                "--rsa-key={}".format(ctx.file.rsa_key.path),
                "--output={}".format(pre.path),
                src.path,
            ] + spx_args,
            executable = ctx.executable._tool,
        )

        # Compute digest to be signed with RSA.
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

        # Compute message to be signed with SPX+.
        if ctx.file.spx_key:
            out = ctx.actions.declare_file(paths.replace_extension(src.basename, ".spx-message"))
            digests.append(out)
            ctx.actions.run(
                outputs = [out],
                inputs = [pre, ctx.executable._tool],
                arguments = [
                    "--rcfile=",
                    "image",
                    "spx-message",
                    "--output={}".format(out.path),
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
        "rsa_key": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "RSA public key to validate this image",
        ),
        "spx_key": attr.label(allow_single_file = True, doc = "SPX public key to validate this image"),
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

def _offline_fake_rsa_sign(ctx):
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

offline_fake_rsa_sign = rule(
    implementation = _offline_fake_rsa_sign,
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
    for sig in ctx.files.rsa_signatures:
        f = _strip_all_extensions(sig.basename)
        if f not in inputs:
            fail("RSA signature {} does not have a corresponding entry in srcs".format(sig.path))
        inputs[f]["rsa_sig"] = sig
    for sig in ctx.files.spx_signatures:
        f = _strip_all_extensions(sig.basename)
        if f not in inputs:
            fail("SPX signature {} does not have a corresponding entry in srcs".format(sig.path))
        if "rsa_sig" not in inputs[f]:
            fail("SPX signature {} does not have corresponding RSA signature".format(sig.path))
        inputs[f]["spx_sig"] = sig

    outputs = []
    for f in inputs:
        if inputs[f].get("bin") == None:
            print("WARNING: No pre-signed binary for", f)
            continue
        if inputs[f].get("rsa_sig") == None:
            print("WARNING: No RSA signature file for", f)
            continue
        out = ctx.actions.declare_file(paths.replace_extension(f, ".signed.bin"))
        action_deps = [
            inputs[f]["bin"],
            inputs[f]["rsa_sig"],
            ctx.executable._tool,
        ]
        args = [
            "--rcfile=",
            "image",
            "manifest",
            "update",
            "--rsa-signature={}".format(inputs[f]["rsa_sig"].path),
        ]
        if inputs[f].get("spx_sig"):
            action_deps.append(inputs[f]["spx_sig"])
            args.append("--spx-signature={}".format(inputs[f]["spx_sig"].path))
        ctx.actions.run(
            outputs = [out],
            inputs = action_deps,
            arguments = args + [
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
        "rsa_signatures": attr.label_list(allow_files = True, doc = "RSA signed digest files"),
        "spx_signatures": attr.label_list(allow_files = True, doc = "SPX+ signed digest files"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)
