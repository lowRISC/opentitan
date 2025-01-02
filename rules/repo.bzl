# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def _bare_repository_impl(rctx):
    rctx.download_and_extract(
        url = rctx.attr.url,
        sha256 = rctx.attr.sha256,
        stripPrefix = rctx.attr.strip_prefix,
    )

    for rpath, lpath in rctx.attr.additional_files.items():
        rctx.symlink(rctx.path(lpath), rpath)
    for rpath, content in rctx.attr.additional_files_content.items():
        rctx.file(rpath, content)

bare_repository = repository_rule(
    implementation = _bare_repository_impl,
    attrs = {
        "url": attr.string(
            mandatory = True,
            doc = "Location of an archive file (exclusive with `local`).",
        ),
        "sha256": attr.string(doc = "SHA256 of the archive."),
        "strip_prefix": attr.string(doc = "Prefix to strip when extracting the archive."),
        "additional_files": attr.string_dict(
            doc = "Additional files to place in the repository (mapping repo filename to local file).",
        ),
        "additional_files_content": attr.string_dict(
            doc = "Additional files to place in the repository (mapping repo filename to strings).",
        ),
    },
    doc = """
        A bare_repository is a repo that needs additional files (such as a BUILD hierarchy)
        added to it.  This is similar to adding a `build_file` to an `http_repository` or
        `new_local_repository` rule, except that multiple files may be added.
    """,
)
