# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")
load("//rules:rv.bzl", "rv_rule")
load("//rules/opentitan:providers.bzl", "get_binary_files")
load("//rules/opentitan:util.bzl", "get_override")

PreSigningBinaryInfo = provider(fields = ["files"])

def key_from_dict(key, attr_name):
    if len(key) == 0:
        return None
    if len(key) != 1:
        fail("Expected exactly one key/value pair for attribute", attr_name)
    key, name = key.items()[0]
    if DefaultInfo in key:
        key_file = key[DefaultInfo].files.to_list()
        if len(key_file) != 1:
            fail("Expected label to refer to exactly one file:", key)
        return struct(
            label = key,
            file = key_file[0],
            name = name,
        )
    return None

def key_ext(rsa, spx):
    if spx:
        return ".{}.{}".format(rsa.name, spx.name)
    else:
        return ".{}".format(rsa.name)

def _presigning_artifacts(ctx, opentitantool, src, manifest, rsa_key, spx_key, basename = None, keyname_in_filenames = False):
    """Create the pre-signing artifacts for a given input binary.

    Applies the manifest and public components of the keys.  Creates the
    digests/messages required for signing.

    Args:
        opentitantool: file; The opentitantool binary.
        src: file; The source binary
        manifest: file; The manifest file.
        rsa_key: struct; The RSA public key.
        spx_key: struct; The SPX+ public key.
        basename: str; Optional basename of the outputs.  Defaults to src.basename.
        keyname_in_filenames: bool; Whether or not to use the key names to construct filenames.
                              Used in test-signing flows to maintain compatibility with existing
                              naming conventions for DV tests.
    Returns:
        struct: A struct containing the pre-signing binary, the digest and spx message files.
    """
    kext = key_ext(rsa_key, spx_key)
    if not basename:
        basename = src.basename
    if keyname_in_filenames:
        basename = paths.replace_extension(basename, kext)
    else:
        basename = paths.replace_extension(basename, "")

    pre = ctx.actions.declare_file("{}.pre-signing".format(basename))
    inputs = [
        src,
        manifest,
        rsa_key.file,
        opentitantool,
    ]
    spx_args = []
    if spx_key:
        spx_args.append("--spx-key={}".format(spx_key.file.path))
        inputs.append(spx_key.file)
    ctx.actions.run(
        outputs = [pre],
        inputs = inputs,
        arguments = [
            "--rcfile=",
            "--quiet",
            "image",
            "manifest",
            "update",
            "--manifest={}".format(manifest.path),
            "--rsa-key={}".format(rsa_key.file.path),
            "--output={}".format(pre.path),
            src.path,
        ] + spx_args,
        executable = opentitantool,
        mnemonic = "PreSigningArtifacts",
    )

    # Compute digest to be signed with RSA.
    digest = ctx.actions.declare_file("{}.digest".format(basename))
    ctx.actions.run(
        outputs = [digest],
        inputs = [pre, opentitantool],
        arguments = [
            "--rcfile=",
            "--quiet",
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
    if spx_key:
        spxmsg = ctx.actions.declare_file("{}.spx-message".format(basename))
        ctx.actions.run(
            outputs = [spxmsg],
            inputs = [pre, opentitantool],
            arguments = [
                "--rcfile=",
                "--quiet",
                "image",
                "spx-message",
                "--output={}".format(spxmsg.path),
                pre.path,
            ],
            executable = opentitantool,
            mnemonic = "PreSigningSpxMessage",
        )
    return struct(pre = pre, digest = digest, spxmsg = spxmsg)

def _local_sign(ctx, opentitantool, digest, rsa_key, spxmsg = None, spx_key = None):
    """Sign a digest with a local on-disk RSA private key.

    Args:
      opentitantool: file; The opentitantool binary.
      digest: file; The digest of the binary to be signed.
      rsa_key: struct; The RSA private key.
      spxmsg: file; The SPX+ message to be signed.
      spx_key: struct; The SPX+ private key.
    Returns:
      file, file: The RSA and SPX signature files.
    """
    rsa_sig = ctx.actions.declare_file(paths.replace_extension(digest.basename, ".rsa_sig"))
    ctx.actions.run(
        outputs = [rsa_sig],
        inputs = [digest, rsa_key.file, opentitantool],
        arguments = [
            "--rcfile=",
            "--quiet",
            "rsa",
            "sign",
            "--input={}".format(digest.path),
            "--output={}".format(rsa_sig.path),
            rsa_key.file.path,
        ],
        executable = opentitantool,
        mnemonic = "LocalRsaSign",
    )

    spx_sig = None
    if spxmsg and spx_key.file:
        spx_sig = ctx.actions.declare_file(paths.replace_extension(spxmsg.basename, ".spx_sig"))
        ctx.actions.run(
            outputs = [spx_sig],
            inputs = [spxmsg, spx_key.file, opentitantool],
            arguments = [
                "--rcfile=",
                "--quiet",
                "spx",
                "sign",
                "--output={}".format(spx_sig.path),
                spxmsg.path,
                spx_key.file.path,
            ],
            executable = opentitantool,
            mnemonic = "LocalSpxSign",
        )

    return rsa_sig, spx_sig

def _post_signing_attach(ctx, opentitantool, pre, rsa_sig, spx_sig):
    """Attach signatures to an unsigned binary.

    Args:
      opentitantool: file; The opentitantool binary.
      pre: file; The pre-signed input binary.
      rsa_sig: file; The RSA-signed digest of the binary.
      spx_sig: file; The SPX-signed message of the binary.
      manifest: file; Optional manifest file.
    Returns:
      file: The signed binary.
    """
    signed = ctx.actions.declare_file(paths.replace_extension(pre.basename, ".signed.bin"))
    inputs = [opentitantool, pre, rsa_sig]
    args = [
        "--rcfile=",
        "--quiet",
        "image",
        "manifest",
        "update",
        "--update-length=false",
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
    rsa_key = key_from_dict(ctx.attr.rsa_key, "rsa_key")
    spx_key = key_from_dict(ctx.attr.spx_key, "spx_key")
    digests = []
    bins = []
    for src in get_binary_files(ctx.attr.srcs):
        artifacts = _presigning_artifacts(
            ctx,
            ctx.executable._tool,
            src,
            ctx.file.manifest,
            rsa_key,
            spx_key,
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
        "rsa_key": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "RSA public key to validate this image",
        ),
        "spx_key": attr.label_keyed_string_dict(
            allow_files = True,
            doc = "SPX public key to validate this image",
        ),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            executable = True,
            cfg = "exec",
        ),
    },
)

def _offline_fake_rsa_sign(ctx):
    outputs = []
    rsa_key = key_from_dict(ctx.attr.rsa_key, "rsa_key")
    for file in ctx.files.srcs:
        sig, _ = _local_sign(ctx, ctx.executable._tool, file, rsa_key)
        outputs.append(sig)
    return [DefaultInfo(files = depset(outputs), data_runfiles = ctx.runfiles(files = outputs))]

offline_fake_rsa_sign = rule(
    implementation = _offline_fake_rsa_sign,
    attrs = {
        "srcs": attr.label_list(allow_files = True, doc = "Digest files to sign"),
        "rsa_key": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "RSA private key to sign this image",
        ),
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
                f, _ = paths.split_extension(file.basename)
                inputs[f] = {"bin": file}
        elif DefaultInfo in src:
            for file in src[DefaultInfo].files.to_list():
                f, _ = paths.split_extension(file.basename)
                inputs[f] = {"bin": file}
    for sig in ctx.files.rsa_signatures:
        f, _ = paths.split_extension(sig.basename)
        if f not in inputs:
            fail("RSA signature {} does not have a corresponding entry in srcs".format(sig.path))
        inputs[f]["rsa_sig"] = sig
    for sig in ctx.files.spx_signatures:
        f, _ = paths.split_extension(sig.basename)
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

def sign_binary(ctx, **kwargs):
    """Sign a binary.

    Args:
      ctx: The rule context.
      kwargs: Overrides of values normally retrived from the context object.
        rsa_key: The RSA signing key.
        spx_key: The SPHINCS+ signing key.
        bin: The input binary.
        manifest: The manifest header.
        _tool: The signing tool (opentitantool).
    Returns:
        A dict of all of the signing artifacts:
          pre: The pre-signing binary (input binary with manifest changes applied).
          digest: The SHA256 hash over the pre-signing binary.
          spxmsg: The SPHINCS+ message to be signed.
          rsa_sig: The RSA signature of the digest.
          spx_sig: The SPHINCS+ signature over the message.
          signed: The final signed binary.
    """
    rsa_key = key_from_dict(get_override(ctx, "attr.rsa_key", kwargs), "rsa_key")
    spx_key = key_from_dict(get_override(ctx, "attr.spx_key", kwargs), "spx_key")
    opentitantool = get_override(ctx, "file._tool", kwargs)

    artifacts = _presigning_artifacts(
        ctx,
        opentitantool,
        get_override(ctx, "file.bin", kwargs),
        get_override(ctx, "file.manifest", kwargs),
        rsa_key,
        spx_key,
        keyname_in_filenames = True,
    )
    rsa_sig, spx_sig = _local_sign(
        ctx,
        opentitantool,
        artifacts.digest,
        rsa_key,
        artifacts.spxmsg,
        spx_key,
    )
    signed = _post_signing_attach(
        ctx,
        opentitantool,
        artifacts.pre,
        rsa_sig,
        spx_sig,
    )
    return {
        "pre": artifacts.pre,
        "digest": artifacts.digest,
        "spxmsg": artifacts.spxmsg,
        "rsa_sig": rsa_sig,
        "spx_sig": spx_sig,
        "signed": signed,
    }

def _sign_bin_impl(ctx):
    result = sign_binary(ctx)
    return [
        DefaultInfo(files = depset([result["signed"]]), data_runfiles = ctx.runfiles(files = [result["signed"]])),
    ]

sign_bin = rv_rule(
    implementation = _sign_bin_impl,
    attrs = {
        "bin": attr.label(allow_single_file = True),
        "rsa_key": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "RSA public key to validate this image",
        ),
        "spx_key": attr.label_keyed_string_dict(
            allow_files = True,
            doc = "SPX public key to validate this image",
        ),
        "manifest": attr.label(allow_single_file = True, mandatory = True),
        # TODO(lowRISC/opentitan:#11199): explore other options to side-step the
        # need for this transition, in order to build the ROM_EXT signer tool.
        "platform": attr.string(default = "@local_config_platform//:host"),
        "_tool": attr.label(
            default = "//sw/host/opentitantool:opentitantool",
            allow_single_file = True,
        ),
    },
)
