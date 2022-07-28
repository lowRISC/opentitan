# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _release_impl(ctx):
    artifacts = []
    runfiles = []
    for k, v in ctx.attr.artifacts.items():
        files = k[DefaultInfo].files.to_list()
        if len(files) > 1:
            fail("Artifacts must produce a single file")
        runfiles.extend(files)
        artifacts.append("'{}#{}'".format(files[0].short_path, v))

    env = "\n".join(["export {}=\"{}\"".format(k, v) for k, v in ctx.attr.env.items()])
    runner = ctx.actions.declare_file(ctx.label.name + ".bash")
    ctx.actions.expand_template(
        template = ctx.file._runner,
        output = runner,
        is_executable = True,
        substitutions = {
            "@@ARTIFACTS@@": " ".join(artifacts),
            "@@ENV@@": env,
            "@@FILES@@": " ".join([f.short_path for f in runfiles]),
            "@@REMOTE@@": ctx.attr.remote,
            "@@SCRIPT@@": ctx.attr.script,
            "@@GH@@": ctx.executable._gh.path,
        },
    )

    return DefaultInfo(
        files = depset([runner]),
        runfiles = ctx.runfiles(files = [ctx.executable._gh] + runfiles),
        executable = runner,
    )

release = rule(
    implementation = _release_impl,
    attrs = {
        "artifacts": attr.label_keyed_string_dict(
            doc = "Mapping of release artifacts to their text descriptions",
            allow_files = True,
        ),
        "remote": attr.string(
            default = "origin",
            doc = "The remote to push the release tag to",
        ),
        "script": attr.string(
            doc = "Script operation to perform before the github release operation",
        ),
        "env": attr.string_dict(
            doc = "Additional environment variables for the script",
        ),
        "_gh": attr.label(
            default = "@com_github_gh//:gh",
            cfg = "exec",
            executable = True,
        ),
        "_runner": attr.label(
            default = "//third_party/github:release.template.bash",
            allow_single_file = True,
        ),
    },
    executable = True,
)
