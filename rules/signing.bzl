# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@bazel_skylib//lib:paths.bzl", "paths")
load("//rules:rv.bzl", "rv_rule")
load("//rules/opentitan:providers.bzl", "get_binary_files")
load("//rules/opentitan:util.bzl", "get_override")
load("//rules/opentitan:toolchain.bzl", "LOCALTOOLS_TOOLCHAIN")
load("//rules:host.bzl", "host_tools_transition")

PreSigningBinaryInfo = provider(fields = ["files"])
SigningToolInfo = provider(fields = ["tool", "data", "env", "location"])
KeySetInfo = provider(fields = ["keys", "selected_key", "profile", "sign", "tool"])

def _label_str(label):
    return "@{}//{}:{}".format(label.workspace_name, label.package, label.name)

def key_from_dict(key, attr_name):
    """Extract the key information from the `key` dict.

    Args:
        key: dict; A signing key and nickname or a keyset and key nickname.
        attr_name: The attribute name (used for error reporting).
    Returns:
        A struct with the key label, the key file and key nickname.
    """
    if len(key) == 0:
        return None
    if len(key) != 1:
        fail("Expected exactly one key/value pair for attribute", attr_name)
    key, name = key.items()[0]
    if "/" in name or "." in name or ":" in name:
        fail("Invalid key nickname for ", str(key), ".  Nickname ", name, " is invalid.")
    if KeySetInfo in key:
        ksi = key[KeySetInfo]
        if ksi.selected_key:
            name = ksi.selected_key
        return struct(
            label = key,
            file = ksi.keys[name],
            name = name,
        )
    elif DefaultInfo in key:
        key_file = key[DefaultInfo].files.to_list()
        if len(key_file) != 1:
            fail("Expected label to refer to exactly one file:", key)
        return struct(
            label = key,
            file = key_file[0],
            name = name,
        )
    return None

def _signing_tool_info(ctx, key, opentitantool):
    """Returns the signing tool information for a given key.

    Args:
        ctx: The rule context object.
        key: The key dict attribute.
        opentitantool: A reference to opentitantool.
    Returns:
        (SigningToolInfo, signing function, profile)
    """
    key, name = key.items()[0]
    if KeySetInfo in key:
        ksi = key[KeySetInfo]
        return ksi.tool, ksi.sign, ksi.profile
    elif DefaultInfo in key:
        toolinfo = SigningToolInfo(
            tool = opentitantool,
            data = [],
            env = {},
            location = "local",
        )
        return toolinfo, _local_sign, None
    fail("Expected a KeySetInfo or DefaultInfo provider")

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

    signing_directives = []
    pre = ctx.actions.declare_file("{}.pre-signing".format(basename))
    inputs = [
        src,
        manifest,
        rsa_key.file,
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
        inputs = [pre],
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
    signing_directives.append(struct(
        command = "rsa-sign",
        id = None,
        label = rsa_key.name,
        format = "Sha256Hash",
        little_endian = True,
        output = "{}.rsa_sig".format(basename),
        input = "{}.digest".format(basename),
    ))

    # Compute message to be signed with SPX+.
    spxmsg = None
    if spx_key:
        spxmsg = ctx.actions.declare_file("{}.spx-message".format(basename))
        ctx.actions.run(
            outputs = [spxmsg],
            inputs = [pre],
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
        # TODO(cfrantz): After adding SPX support to hsmtool, append an appropriate
        # signing directive here.

    return struct(pre = pre, digest = digest, spxmsg = spxmsg, script = signing_directives)

def _local_sign(ctx, tool, digest, rsa_key, spxmsg = None, spx_key = None, profile = None):
    """Sign a digest with a local on-disk RSA private key.

    Args:
      tool: SigningToolInfo; A provider refering to the opentitantool binary.
      digest: file; The digest of the binary to be signed.
      rsa_key: struct; The RSA private key.
      spxmsg: file; The SPX+ message to be signed.
      spx_key: struct; The SPX+ private key.
      profile: str; The token profile.  Not used by this function.
    Returns:
      file, file: The RSA and SPX signature files.
    """
    rsa_sig = ctx.actions.declare_file(paths.replace_extension(digest.basename, ".rsa_sig"))
    ctx.actions.run(
        outputs = [rsa_sig],
        inputs = [digest, rsa_key.file],
        arguments = [
            "--rcfile=",
            "--quiet",
            "rsa",
            "sign",
            "--input={}".format(digest.path),
            "--output={}".format(rsa_sig.path),
            rsa_key.file.path,
        ],
        executable = tool.tool,
        mnemonic = "LocalRsaSign",
    )

    spx_sig = None
    if spxmsg and spx_key.file:
        spx_sig = ctx.actions.declare_file(paths.replace_extension(spxmsg.basename, ".spx_sig"))
        ctx.actions.run(
            outputs = [spx_sig],
            inputs = [spxmsg, spx_key.file],
            arguments = [
                "--rcfile=",
                "--quiet",
                "spx",
                "sign",
                "--output={}".format(spx_sig.path),
                spxmsg.path,
                spx_key.file.path,
            ],
            executable = tool.tool,
            mnemonic = "LocalSpxSign",
        )

    return rsa_sig, spx_sig

def _hsmtool_sign(ctx, tool, digest, rsa_key, spxmsg = None, spx_key = None, profile = None):
    """Sign a digest with a local on-disk RSA private key.
    Args:
      tool: file; A SigningToolInfo provider referring to the hsmtool binary.
      digest: file; The digest of the binary to be signed.
      rsa_key: struct; The RSA private key.
      spxmsg: file; The SPX+ message to be signed.
      spx_key: struct; The SPX+ private key.
      profile: str; The hsmtool profile.
    Returns:
      file, file: The RSA and SPX signature files.
    """
    if spxmsg or spx_key:
        fail("hsmtool currently does not support SPX+ signing")
    if not profile:
        fail("Missing the `hsmtool` profile")
    rsa_sig = ctx.actions.declare_file(paths.replace_extension(digest.basename, ".rsa-sig"))
    ctx.actions.run(
        outputs = [rsa_sig],
        inputs = [digest, rsa_key.file, tool.tool] + tool.data,
        arguments = [
            "--quiet",
            "--lockfile=/tmp/hsmtool.lock",
            "--profile={}".format(profile),
            "rsa",
            "sign",
            "--little-endian",
            "--format=sha256-hash",
            "--label={}".format(rsa_key.name),
            "--output={}".format(rsa_sig.path),
            digest.path,
        ],
        executable = tool.tool,
        execution_requirements = {
            "no-sandbox": "",
        },
        env = tool.env,
        mnemonic = "HsmtoolRsaSign",
    )
    return rsa_sig, None

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
    inputs = [pre, rsa_sig]
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
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    rsa_key = key_from_dict(ctx.attr.rsa_key, "rsa_key")
    spx_key = key_from_dict(ctx.attr.spx_key, "spx_key")
    digests = []
    bins = []
    script = []
    for src in get_binary_files(ctx.attr.srcs):
        artifacts = _presigning_artifacts(
            ctx,
            tc.tools.opentitantool,
            src,
            ctx.file.manifest,
            rsa_key,
            spx_key,
        )
        bins.append(artifacts.pre)
        digests.append(artifacts.digest)
        script.extend(artifacts.script)
        if artifacts.spxmsg:
            digests.append(artifacts.spxmsg)

    default_files = digests
    if script:
        script_file = ctx.actions.declare_file("{}.json".format(ctx.attr.name))
        ctx.actions.write(script_file, json.encode_indent(script, indent = "  ") + "\n")
        default_files.append(script_file)

    return [
        DefaultInfo(files = depset(default_files), data_runfiles = ctx.runfiles(files = default_files)),
        PreSigningBinaryInfo(files = depset(bins)),
        OutputGroupInfo(digest = depset(digests), binary = depset(bins), script = depset([script_file])),
    ]

offline_presigning_artifacts = rule(
    implementation = _offline_presigning_artifacts,
    attrs = {
        "srcs": attr.label_list(allow_files = True, doc = "Binary files to generate digests for"),
        "manifest": attr.label(allow_single_file = True, doc = "Manifest for this image"),
        "rsa_key": attr.label_keyed_string_dict(
            providers = [[KeySetInfo], [DefaultInfo]],
            allow_files = True,
            mandatory = True,
            doc = "RSA public key to validate this image",
        ),
        "spx_key": attr.label_keyed_string_dict(
            providers = [[KeySetInfo], [DefaultInfo]],
            allow_files = True,
            doc = "SPX public key to validate this image",
        ),
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def _offline_fake_rsa_sign(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    outputs = []
    rsa_key = key_from_dict(ctx.attr.rsa_key, "rsa_key")
    tool, _, _ = _signing_tool_info(ctx, ctx.attr.rsa_key, tc.tools.opentitantool)
    for file in ctx.files.srcs:
        sig, _ = _local_sign(ctx, tool, file, rsa_key)
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
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
    doc = "Create detached signatures using on-disk private keys via opentitantool.",
)

def _offline_signature_attach(ctx):
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
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
            tc.tools.opentitantool,
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
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def sign_binary(ctx, opentitantool, **kwargs):
    """Sign a binary.

    Args:
      ctx: The rule context.
      opentitantool: An opentitantool FilesToRun provider.
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
    rsa_attr = get_override(ctx, "attr.rsa_key", kwargs)
    rsa_key = key_from_dict(rsa_attr, "rsa_key")
    spx_key = key_from_dict(get_override(ctx, "attr.spx_key", kwargs), "spx_key")

    artifacts = _presigning_artifacts(
        ctx,
        opentitantool,
        get_override(ctx, "file.bin", kwargs),
        get_override(ctx, "file.manifest", kwargs),
        rsa_key,
        spx_key,
        keyname_in_filenames = True,
    )
    tool, signing_func, profile = _signing_tool_info(ctx, rsa_attr, opentitantool)
    rsa_sig, spx_sig = signing_func(
        ctx,
        tool,
        artifacts.digest,
        rsa_key,
        artifacts.spxmsg,
        spx_key,
        profile,
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
    tc = ctx.toolchains[LOCALTOOLS_TOOLCHAIN]
    result = sign_binary(ctx, tc.tools.opentitantool)
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
    },
    toolchains = [LOCALTOOLS_TOOLCHAIN],
)

def _signing_tool(ctx):
    env = {k: ctx.expand_location(v, ctx.attr.data) for k, v in ctx.attr.env.items()}
    return [SigningToolInfo(
        tool = ctx.executable.tool,
        data = ctx.files.data,
        env = env,
        location = ctx.attr.location,
    )]

signing_tool = rule(
    implementation = _signing_tool,
    attrs = {
        "tool": attr.label(
            mandatory = True,
            executable = True,
            cfg = host_tools_transition,
            doc = "The signing tool binary",
        ),
        "data": attr.label_list(
            allow_files = True,
            cfg = "exec",
            doc = "Additional files needed by the signing tool",
        ),
        "env": attr.string_dict(
            doc = "Environment variables needed by the signing tool",
        ),
        "location": attr.string(
            mandatory = True,
            values = ["local", "token"],
            doc = "The location of private keys.  Local keys are on-disk and are typically used for simulation or emulation (FPGA) test scenarios.  Token keys are held in a secure token or HSM and are typically used for signing artifacts for real chips.",
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
)

def _keyset(ctx):
    keys = {}
    for k, v in ctx.attr.keys.items():
        keyfile = k.files.to_list()
        if len(keyfile) != 1:
            fail("keyset key labels must resolve to exactly one file.")
        keys[v] = keyfile[0]

    tool = ctx.attr.tool[SigningToolInfo]
    if tool.location == "local" and ctx.attr.profile != "local":
        print("WARNING: The selected signing tool {} cannot work with keyset profile `{}`.".format(
            _label_str(ctx.attr.tool.label),
            ctx.attr.profile,
        ))

    selected_key = ctx.build_setting_value
    if selected_key and selected_key not in keys:
        fail("Key name", selected_key, "is not in ", keys.keys())
    if ctx.attr.profile == "local":
        sign = _local_sign
    else:
        sign = _hsmtool_sign
    return [KeySetInfo(keys = keys, selected_key = selected_key, profile = ctx.attr.profile, sign = sign, tool = tool)]

keyset = rule(
    implementation = _keyset,
    build_setting = config.string(flag = True),
    attrs = {
        "keys": attr.label_keyed_string_dict(
            allow_files = True,
            mandatory = True,
            doc = "A mapping of key files to key names.  When a key file is a public key whose private component is held in an HSM, the name should be the same as the HSM label of that key.",
        ),
        "profile": attr.string(
            mandatory = True,
            doc = "The hsmtool profile entry (in $XDG_CONFIG_HOME/hsmtool/profiles.json) associated with these keys or the value `local` for on-disk private keys.",
        ),
        "tool": attr.label(
            mandatory = True,
            providers = [SigningToolInfo],
        ),
    },
)
