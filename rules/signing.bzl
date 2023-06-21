# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")

PreSigningBinaryInfo = provider(fields = ["files"])

def _presigning_artifacts(ctx, opentitantool, src, manifest, rsa_key_file, spx_key_file):
    """Create the pre-signing artifacts for a given input binary.

    Applies he manifest and public components of the keys.  Creates the
    digests/messages required for signing.

    Args:
        opentitantool: file; The opentitantool binary.
        src: file; The source binary
        manifest: file; The manifest file.
        rsa_key_file: file; The RSA public key.
        spx_key_file: file; The SPX+ public key.
    Returns:
        struct: A struct containing the pre-signing binary, the digest and spx message files.
    """
    pre = ctx.actions.declare_file(paths.replace_extension(src.basename, ".pre-signing"))
    inputs = [
        src,
        manifest,
        rsa_key_file,
        opentitantool,
    ]
    spx_args = []
    if spx_key_file:
        spx_args.append("--spx-key={}".format(spx_key_file.path))
        inputs.append(spx_key_file)
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
        executable = opentitantool,
        mnemonic = "PreSigningArtifacts",
    )

    # Compute digest to be signed with RSA.
    digest = ctx.actions.declare_file(paths.replace_extension(src.basename, ".digest"))
    ctx.actions.run(
        outputs = [digest],
        inputs = [pre, opentitantool],
        arguments = [
            "--rcfile=",
            "image",
            "digest",
            "--bin={}".format(digest.path),
            pre.path,
        ],
        executable = opentitantool,
        mnemonic = "PreSigningDigest",
    )

    # Compute message to be signed with SPX+.
    spxmsg = None
    if spx_key_file:
        spxmsg = ctx.actions.declare_file(paths.replace_extension(src.basename, ".spx-message"))
        ctx.actions.run(
            outputs = [spxmsg],
            inputs = [pre, opentitantool],
            arguments = [
                "--rcfile=",
                "image",
                "spx-message",
                "--output={}".format(spxmsg.path),
                pre.path,
            ],
            executable = opentitantool,
            mnemonic = "PreSigningSpxMessage",
        )
    return struct(pre = pre, digest = digest, spxmsg = spxmsg)

def _local_rsa_sign(ctx, opentitantool, digest, rsa_key_file):
    """Sign a digest with a local on-disk RSA private key.

    Args:
      opentitantool: file; The opentitantool binary.
      digest: file; The digest of the binary to be signed.
      rsa_key_file: file; The private key.
    Returns:
      file: The signature over the digest.
    """
    signature = ctx.actions.declare_file(paths.replace_extension(digest.basename, ".sig"))
    ctx.actions.run(
        outputs = [signature],
        inputs = [digest, rsa_key_file, opentitantool],
        arguments = [
            "--rcfile=",
            "rsa",
            "sign",
            "--input={}".format(digest.path),
            "--output={}".format(signature.path),
            rsa_key_file.path,
        ],
        executable = opentitantool,
        mnemonic = "LocalRsaSign",
    )
    return signature

def _post_signing_attach(ctx, opentitantool, pre, rsa_sig, spx_sig):
    """Attach signatures to an unsigned binary.

    Args:
      opentitantool: file; The opentitantool binary.
      pre: file; The pre-signed input binary.
      rsa_sig: file; The RSA-signed digest of the binary.
      spx_sig: file; The SPX-signed message of the binary.
    Returns:
      file: The signed binary.
    """
    signed = ctx.actions.declare_file(paths.replace_extension(pre.basename, ".signed.bin"))
    inputs = [opentitantool, pre, rsa_sig]
    args = [
        "--rcfile=",
        "image",
        "manifest",
        "update",
        "--rsa-signature={}".format(rsa_sig.path),
        "--output={}".format(signed.path),
        pre.path,
    ]
    if spx_sig:
        inputs.append(spx_sig)
        args.append("--spx-signature={}".format(spx_sig.path))

    ctx.actions.run(
        outputs = [signed],
        inputs = inputs,
        arguments = args,
        executable = opentitantool,
        mnemonic = "PostSigningAttach",
    )
    return signed

def _offline_presigning_artifacts(ctx):
    digests = []
    bins = []
    for src in ctx.files.srcs:
        artifacts = _presigning_artifacts(
            ctx,
            ctx.executable._tool,
            src,
            ctx.file.manifest,
            ctx.file.rsa_key,
            ctx.file.spx_key,
        )
        bins.append(artifacts.pre)
        digests.append(artifacts.digest)
        if artifacts.spxmsg:
            digests.append(artifacts.spxmsg)
    return [
        DefaultInfo(files = depset(digests), data_runfiles = ctx.runfiles(files = digests)),
        PreSigningBinaryInfo(files = depset(bins)),
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
        sig = _local_rsa_sign(ctx, ctx.executable._tool, file, ctx.file.key_file)
        outputs.append(sig)
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
        if PreSigningBinaryInfo in src:
            for file in src[PreSigningBinaryInfo].files.to_list():
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
        out = _post_signing_attach(
            ctx,
            ctx.executable._tool,
            inputs[f]["bin"],
            inputs[f]["rsa_sig"],
            inputs[f].get("spx_sig"),
        )
        outputs.append(out)
    return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

offline_signature_attach = rule(
    implementation = _offline_signature_attach,
    attrs = {
        "srcs": attr.label_list(allow_files = True, providers = [PreSigningBinaryInfo], doc = "Binary files to sign"),
        "rsa_signatures": attr.label_list(allow_files = True, doc = "RSA signed digest files"),
        "spx_signatures": attr.label_list(allow_files = True, doc = "SPX+ signed digest files"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)
