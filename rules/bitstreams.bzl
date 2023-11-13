# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to interface with bitstreams caches

This Starlark library comprises several rules for interfacing with bitstreams
caches.

`bitstreams_repo` is a `repository_rule` that reaches out to a remote bitstreams
cache, downloads files to create a local cache, and creates a @bitstreams
external repository (for bazel) with filegroup targets that represent the
designs present in the selected cache entry.

The rest of the rules are ordinary build rules for creating cache entries,
which ultimately are tarballs containing the bitstream build outputs and a
manifest file (manifest.json at the root of the tarball) that describes how
the files are grouped to represent a particular design.

A full cache entry contains information about multiple designs, but the rules
below also create a notion of "manifest fragments," which are essentially
conforming directories with a manifest and the files for a single design. These
fragments combine to create a full cache entry. Bazel targets are made aware of
these fragments via the BitstreamManifestFragmentInfo provider, which contains
all the relevant information to process them.

The cache entry is broken into fragments here to enable different build flows,
where bitstreams may be built on independent agents / bazel services and may be
passed to downstream jobs as though they were part of a bitstreams cache. In
addition, the cache entry to be uploaded may continue to be made up of both
freshly-built bitstreams and cached bitstreams (i.e. mix-and-match). Optimized
build flows may not build every bitstream merely because one isolated design's
files have changed.

For the manifest.json file, the schema describing its format is at
`//rules/scripts:bitstreams_manifest_schema` at the time of writing.

The rules:
    - `bitstream_generate_manifest_fragment`
        - Takes the outputs of a bitstream build and generates a manifest
          fragment.
    - `bitstreams_fragment_from_manifest`
        - Takes a cache entry (e.g. from the @bitstreams external repository)
          and creates a manifest fragment for a selected design.

Together, these rules enable flexibility in choosing whether to build a
particular bitstream or use cached version for the next cache entry, for each
design (i.e. mix-and-match).
"""

load("@python3//:defs.bzl", "interpreter")
load("@ot_python_deps//:requirements.bzl", "all_requirements")

def _make_pythonpath(rctx):
    # Create a PYTHONPATH with all the pip deps from requirements.txt
    directories = [
        rctx.path(Label(pip_req + ":BUILD.bazel")).dirname
        for pip_req in all_requirements
    ]
    pythonpath = ":".join([str(directory) for directory in directories])
    return pythonpath

def _bitstreams_repo_impl(rctx):
    # First, check if an existing pre-built bitstream cache repo exists, and if
    # so, use it instead of building one.
    cache_path = rctx.os.environ.get(
        "BAZEL_BITSTREAMS_CACHE",
        rctx.attr.cache,
    )
    result = rctx.execute(
        [
            rctx.path(rctx.attr.python_interpreter),
            rctx.attr._cache_manager,
            "--build-file=BUILD.bazel",
            "--bucket-url={}".format(rctx.attr.bucket_url),
            "--cache={}".format(cache_path),
            "--refresh-time={}".format(rctx.attr.refresh_time),
        ],
        environment = {
            "PYTHONPATH": _make_pythonpath(rctx),
        },
        quiet = False,
    )
    if result.return_code != 0:
        fail("Bitstream cache not initialized properly.")

# The bitstream repo should be evaluated with `bazel sync --configure` after
# every Git checkout. Once the cache is initialized, a typical invocation will
# find the latest cached artifacts and map them to Bazel targets.
#
# The `refresh_time` sets the interval at which the cache manager will
# check for new bitstreams.
#
# By default, the cache manager will configure the latest available bitstream
# as the default bitstream.  It will refresh every 18 hours.
#
# The behavior of the cache manager can be controlled via the BITSTREAM
# environment variable.  The environment variable can be any command line
# arguments accepted by the cache manager script.
#
# For example, to force a refresh of the cache:
# BITSTREAM=--refresh bazel build @bitstreams//...
#
# To use an exact bitstream in a test:
# BITSTREAM=3732655dbd225b5c1ae94a79b54cc9dc8cd8e391 bazel test <label>
#
# You can use any valid git commit identifier to select a bitstream:
# BITSTREAM=HEAD~1 bazel test <label>
#
# If you ask for a bitstream that does not exist in the GCP bucket, the
# next oldest bitstream will be chosen.
bitstreams_repo = repository_rule(
    implementation = _bitstreams_repo_impl,
    attrs = {
        "bucket_url": attr.string(
            doc = "Location of the GCP bitstream bucket.",
            default = "https://storage.googleapis.com/opentitan-bitstreams/",
        ),
        "cache": attr.string(
            doc = "Location of bitstreams cache.",
            default = "~/.cache/opentitan-bitstreams",
        ),
        "refresh_time": attr.int(
            doc = "How often to check for new bitstreams (seconds).",
            default = 18 * 3600,  # Refresh every 18h
        ),
        "python_interpreter": attr.label(
            default = interpreter,
            allow_single_file = True,
            doc = "Python interpreter to use.",
        ),
        "_cache_manager": attr.label(
            default = Label("//rules/scripts:bitstreams_workspace.py"),
            allow_files = True,
        ),
    },
    environ = ["BAZEL_BITSTREAMS_CACHE", "BITSTREAM"],
    # This rule depends on the Git repository, but there's no ergonomic way to
    # encode the dependency in Bazel. Instead, indicate that the rule depends on
    # something outside of Bazel's dependency graph and rely on the user calling
    # `bazel sync --configure` when checking out new revisions. For historical
    # context, see <https://github.com/lowRISC/opentitan/issues/16832>.
    configure = True,
)

# Bitstream manifests follow a schema written in the JSON Schema language, and
# all file paths in the manifest are relative to the manifest's directory.
# The tools provided to operate on bitstream cache entries currently create
# directories with the following layout:
#   <manifest_dir>:
#       design_name_1:
#           bitstream.bit
#           mem_map_1.mmi
#           mem_map_2.mmi
#       design_name_2:
#           bitstream.bit
#           mem_map_1.mmi
#           mem_map_2.mmi
# Thus, the tools impose one additional requirement beyond the JSON schema, that
# every file in a design's fileset has a unique basename.
BitstreamManifestFragmentInfo = provider(
    doc = """Collection of variables describing a manifest fragment.""",
    fields = {
        "fragment": "Manifest fragment dictionary",
        "srcs": "Depset of files that are described by this manifest fragment",
    },
)

def _bitstream_generate_manifest_fragment(design, srcs, bitstream, memory_maps):
    fragment = {
        "schema_version": 2,
        "designs": {},
    }
    metadata = {}
    deps = []
    for src in srcs:
        if OutputGroupInfo not in src:
            msg = "Unexpected source {} without OutputGroupInfo provider"
            fail(msg.format(src))
        output_groups = src[OutputGroupInfo]
        if bitstream in output_groups:
            bitstream_outputs = output_groups[bitstream].to_list()
            if len(bitstream_outputs) != 1:
                fail("Too many bitstream outputs for output group")
            file_path = "/".join([design, bitstream_outputs[0].basename])
            metadata["bitstream"] = {
                "file": file_path,
                "build_target": str(src.label),
            }
            deps.append(bitstream_outputs[0])

        memory_map_info = {}
        for output_group, mem_id in memory_maps.items():
            if output_group in output_groups:
                memory_files = output_groups[output_group].to_list()
                if len(memory_files) != 1:
                    fail("Too many memory map outputs for output group")
                file_path = "/".join([design, memory_files[0].basename])
                memory_map_info[mem_id] = {
                    "file": file_path,
                    "build_target": str(src.label),
                }
                deps.append(memory_files[0])
        metadata["memory_map_info"] = memory_map_info
    fragment["designs"][design] = metadata
    return (fragment, deps)

def _bitstream_manifest_fragment_impl(ctx):
    outputs = []
    fragment_file = ctx.actions.declare_file(ctx.attr.name + "/manifest.json")
    (fragment, deps) = _bitstream_generate_manifest_fragment(
        ctx.attr.design,
        ctx.attr.srcs,
        ctx.attr.bitstream,
        ctx.attr.memory_maps,
    )
    for dep in deps:
        file_path = "/".join([ctx.attr.name, ctx.attr.design, dep.basename])
        symlink = ctx.actions.declare_file(file_path)
        ctx.actions.symlink(output = symlink, target_file = dep)
        outputs.append(symlink)
    ctx.actions.write(fragment_file, json.encode_indent(fragment))
    outputs.append(fragment_file)
    return [
        DefaultInfo(
            files = depset(outputs),
        ),
        BitstreamManifestFragmentInfo(
            fragment = fragment_file,
            srcs = depset(outputs),
        ),
    ]

bitstream_manifest_fragment = rule(
    doc = """Generates a bitstream cache manifest fragment from a built design.

        The rules creates a directory with the same name as the build target's,
        places the selected files into the directory, and generates a
        manifest.json file with the metadata describing this manifest fragment.
        This rule is purely implemented in bazel, and symlinks are used instead
        of copies to avoid redundant large files.
        """,
    implementation = _bitstream_manifest_fragment_impl,
    attrs = {
        "design": attr.string(
            doc = "The design's name, a unique identifier to group the files.",
            mandatory = True,
        ),
        "srcs": attr.label_list(
            doc = "The labels or files that make up this cache entry.",
            allow_empty = False,
            allow_files = True,
            providers = [OutputGroupInfo],
        ),
        "bitstream": attr.string(
            doc = "The output group for the programmable bitstream file.",
            mandatory = True,
        ),
        "memory_maps": attr.string_dict(
            doc = """A map from memory map files' output groups to their memory
IDs (e.g. rom, otp, etc.)""",
        ),
    },
)

def _bitstream_fragment_from_manifest_impl(ctx):
    fragment_file = ctx.actions.declare_file(ctx.attr.name + "/manifest.json")
    outputs = [fragment_file]
    for src in ctx.files.srcs:
        if src.path == ctx.file.manifest.path:
            continue
        file_path = "/".join([ctx.attr.name, ctx.attr.design, src.basename])
        symlink = ctx.actions.declare_file(file_path)
        ctx.actions.symlink(output = symlink, target_file = src)
        outputs.append(symlink)

    inputs = [ctx.file.manifest]
    inputs.extend(ctx.files._schema)
    inputs.extend(ctx.files._fragment_extractor_tool)
    args = ctx.actions.args()
    args.add("--manifest", ctx.file.manifest.path)
    args.add("--schema", ctx.file._schema.path)
    args.add("--design", ctx.attr.design)
    args.add("--out", fragment_file.dirname)
    ctx.actions.run(
        outputs = [fragment_file],
        inputs = inputs,
        executable = ctx.executable._fragment_extractor_tool,
        arguments = [args],
    )
    outputs.append(fragment_file)
    return [
        DefaultInfo(
            files = depset(outputs),
        ),
        BitstreamManifestFragmentInfo(
            fragment = fragment_file,
            srcs = depset(outputs),
        ),
    ]

bitstream_fragment_from_manifest = rule(
    doc = """Creates the selected design's manifest fragment from a full
        manifest.

        This rule uses the bitstreams_fragment_from_manifest.py Python script
        to analyze the manifest and extract the design's manifest fragment. A
        new directory is created, and currently, the symlinks are done in
        Starlark for explicit tracking, though the Python script also has the
        capability to generate them. The output of this rule is the same as
        bitstreams_fragment_from_manifest, a manifest fragment directory with
        symlnks pointing to bitstream and MMI files and a manifest.json tailored
        to the one design.

        This rule enables reusing components from a cache entry, before they are
        assembled together other designs that were freshly-built, to make a new
        cache entry.
        """,
    implementation = _bitstream_fragment_from_manifest_impl,
    attrs = {
        "design": attr.string(
            doc = "The design's name, a unique identifier to group the files.",
            mandatory = True,
        ),
        "manifest": attr.label(
            doc = "Label referencing the manifest to extract from.",
            allow_single_file = True,
            mandatory = True,
        ),
        "srcs": attr.label_list(
            doc = "The labels for files that make up this cache entry.",
            allow_empty = False,
            allow_files = True,
            mandatory = True,
        ),
        "_schema": attr.label(
            doc = "Path to bitstream cache manifest schema",
            default = "//rules/scripts:bitstreams_manifest_schema",
            allow_single_file = True,
        ),
        "_fragment_extractor_tool": attr.label(
            doc = "Path to bitstream manifest fragment extractor tool",
            executable = True,
            default = "//util/py/scripts:bitstreams_fragment_from_manifest",
            cfg = "exec",
        ),
    },
)
