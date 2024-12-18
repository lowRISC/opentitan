# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
The only extension in this file is the `ot_py_for_repo` extension.
This extension creates repositories that allow to execute python
code in repository rules, where the normal python rules are
unavailable.

In order to use this extension, first import it as usual:
```
ot_py_for_repo = use_extension("//third_party/python:extension.bzl", "ot_py_for_repo")
```

Now assume that we have already setup a python interpreter as follows:
```
python = use_extension("@rules_python//python/extensions:python.bzl", "python")
python.toolchain(...)
use_repo(python, "pythons_hub")
register_toolchains("@pythons_hub//:all")
# Here it is very important to use the **host** python repository and not
# the usual repository. This repository contaisn symlinks to the actual interpreter.
use_repo(python3_host = "python_3_9_host")
```

Further assume that we have setup pip as follows:
```
pip = use_extension("@rules_python//python/extensions:pip.bzl", "pip")
pip.parse(
    hub_name = "ot_python_deps",
    python_version = "3.9",
    requirements_lock = ...,
)
use_repo(pip, "ot_python_deps")
```

Now we would like to be able to use the python interpret with some pip dependencies,
say "hjson". We need to register this intention with the extension and it will
create a repository for us.
```
ot_py_for_repo.register(
    # You can choose the following name arbitrarily.
    repo_name = "my_favorite_name",
    # Here we need to point to the interpret in the repo used above.
    python = "@python3_host//:python",
    packages = [
        # For each package, we need to pass a label to any file at the root
        # of the repository created by rules_python. The general scheme is:
        # <hub_name>_<pyversion>_<package>
        "@ot_python_deps_39_hjson//:BUILD.bazel"
    ],
)
use_repo(ot_py_for_repo, "my_favorite_name")
```

Now that we have registered our usage. We can use this interpreter by
simply using the label "@my_favorite_name//:python". This executable
can be called as if it a normal python interpreter. It will automatically
set the PYTHONPATH to the correct value before running so that all the packages
listed at the registrering step at available.

A quick way to test it is as follows:
```
bazel run @my_favorite_name//:python
```
"""

PYTHON_INTERPRETER_TEMPLATE = """
# Call the real interpreter with all the arguments
PYTHONPATH={pythonpath} {python_binary} "$@"
"""

BUILD_CONTENT = """
exports_files([
    "python"
])
"""

def _ot_py_for_repo_repo_impl(ctx):
    import_dirs = [
        # We have a path to any file inside the repository, we get
        # the parent and then the site packages.
        str(ctx.path(pkg).dirname.get_child("site-packages"))
        for pkg in ctx.attr.packages
    ]
    content = PYTHON_INTERPRETER_TEMPLATE.format(
        python_binary = ctx.path(ctx.attr.python),
        pythonpath = ":".join(import_dirs),
    )
    ctx.file("python", content, executable = True)
    ctx.file("BUILD", BUILD_CONTENT)

ot_py_for_repo_repo = repository_rule(
    implementation = _ot_py_for_repo_repo_impl,
    doc = """
        Create a repository containing a single bash binary: python.
        This binary act as a python interpreter and will setup
        everything so that the required packages can be used.
    """,
    attrs = {
        "python": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "Path to the python interpreter",
        ),
        "packages": attr.label_list(
            default = [],
            doc = """
            List of python pip dependencies: point to any file at the root of the repositories
            For example, @@ot_python_deps_39_hjson//:BUILD.bazel
            """,
        ),
    },
)

_register = tag_class(
    attrs = {
        "repo_name": attr.string(
            mandatory = True,
            doc = "Name of the repository to create",
        ),
        "python": attr.label(
            allow_single_file = True,
            mandatory = True,
            doc = "Path to the python interpreter",
        ),
        "packages": attr.label_list(
            default = [],
            doc = "List of python pip dependencies: point to the :pkg inside the bazel repositories",
        ),
    },
)

def _ot_py_for_repo_impl(ctx):
    for mod in ctx.modules:
        for reg in mod.tags.register:
            ot_py_for_repo_repo(
                name = reg.repo_name,
                python = reg.python,
                packages = reg.packages,
            )

    return ctx.extension_metadata(reproducible = True)

ot_py_for_repo = module_extension(
    implementation = _ot_py_for_repo_impl,
    tag_classes = {
        "register": _register,
    },
    doc = "Extensions to allow the use of the Python interpreter and pip dependencies in the repository rules",
)
