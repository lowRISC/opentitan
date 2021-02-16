def _sysroot_archive_impl(repository_ctx):
    repository_ctx.download_and_extract(
        url = repository_ctx.attr.urls[0],
        sha256 = repository_ctx.attr.sha256,
        output = "root",
    )
    repository_ctx.file("sysroot", content = "")
    repository_ctx.file("BUILD", content = """exports_files(glob(["**/*"]))""")

sysroot_archive = repository_rule(
    _sysroot_archive_impl,
    attrs = {
        "urls": attr.string_list(),
        "sha256": attr.string(),
    },
)
