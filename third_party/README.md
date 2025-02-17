# OpenTitan external dependencies

OpenTitan depends on a number of third-party components.

These include:

* Bazel rule dependencies (e.g. `rules_rust` for building Rust code).
* Package dependencies (e.g. Rust crates, Python packages, APT packages).
* Source dependencies (e.g. the source for OpenOCD, test vectors).
* External silicon RTL.

This document describes how we manage each of these kinds of dependency.

## Bazel rule dependencies

This repository forms a Bazel module described by the `MODULE.bazel` file at the
root. We use a feature called [Bzlmod] to depend on other modules by adding `bazel_dep`
directives to the `MODULE.bazel` file.

Some Bazel modules expose "extensions" for extra features such as registering
toolchains and downloading package dependencies. This example uses an extension from
`rules_python` to create a specific Python toolchain that we can register:

```python
python = use_extension("@rules_python//python/extensions:python.bzl", "python")
python.toolchain(
    is_default = True,
    python_version = "3.10",
)
use_repo(python, "pythons_hub")
register_toolchains("@pythons_hub//:all")
```

Extensions generate Bazel repositories (`pythons_hub` in this example) that
can be imported our module's namespace.

If a Bazel dependency requires lots of extension calls, consider extracting them
to a new `third_party/${name}/${name}.MODULE.bazel` file and `include`ing it in
the main `MODULE.bazel`.

[Bzlmod]: https://bazel.build/external/overview#bzlmod

## Package dependencies

We tend to use an ecosystem's package definition format to list our dependencies and
then install them manually or within Bazel depending on how they're used.

These package manifests can be found at:

* Python: `pyproject.toml` in the root of the repository.
* Rust: `third_party/rust/Cargo.toml` for most dependencies.

  * We have additional `Cargo.toml` files to allow certain projects to use
  different dependency versions.

* Bzlmod: `MODULE.bazel` in the root of the repository.
* APT: `apt-requirements.txt` in the root of the repository.

Some of these manifests have lock files which ensure we're using exactly the same
versions on different builds. These must be kept up to date with changes to the
manifests. Use `./ci/scripts/check-lock-files.sh` to check and regenerate lock files.

## Source dependencies

Sometimes we need access to external source and data files. These are brought into
our Bazel module using Bzlmod extensions.

To add a new source dependency:

1. Create a new file `third_party/my_dep/extensions.bzl` for your extension.
2. Create a Starlark function to download any repositories you need:

   ```python
   def _my_repos():
       http_archive(
           name = "my_repo",
           url = "...",
           sha256 = "...",
       )
   ```

3. Create a Bzlmod extension for your function:

   ```python
   my_extension = module_extension(
       implementation = lambda _: _my_repos(),
   )
   ```

4. Use your extension from `MODULE.bazel` like you would with external modules:

   ```python
   my_extension = use_extension("//third_party/my_dep:extensions.bzl", "my_extension")
   use_repo(my_extension, "my_repo")
   ```

You should now be able to access your repository's files from Bazel using
`@my_repo//:path/to/file`.

## Third-party Silicon IP

Currently, silicon uses a separate vendoring mechanism: `util/vendor.py`.
There are no concrete plans to migrate off of this script for hardware. This
script should not be used for new software dependencies; instead, use the
`//third_party` directory and Bzlmod extensions instead.
