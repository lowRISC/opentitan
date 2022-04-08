OpenTitan `//third_party`
==========

OpenTitan depends on a number of third party components. This directory consists of:
- Bazel files describing how to acquire them from the Internet, and incorporate them
  into the OpenTitan workspace.
- Glue code for plugging dependencies into first-party software.

Every dependency lives in a subdirectory; each subdirectory consists of at least three
files:
1.  A (usually empty) `BUILD` file to specify that file as a Bazel package.
2.  A `repos.bzl`, which exports a macro called `blah_repos()` that can be called in the
    `WORKSPACE` to declare the remote repositories required for the dependency.
3.  A `deps.bzl`, which exports a macro called `blah_deps()` that uses the repositories
    created by `blah_repos()` to set up any other requirements of the dependency. It must
    be called in the `WORKSPACE` file after `blah_repos()` is called. Some dependencies
    can skip this step.

Thus, for each third party dependency, a stanza like the following should appear in the
`WORKSPACE`:

```bazel
load("//third_party/<dep>/repos.bzl", "<dep>_repos")
<dep>_repos()
load("//third_party/<dep>/deps.bzl", "<dep>_deps")
<dep>_deps()
```

In some cases, the `BUILD` file for the dependency will declare rules for tests, such as
`rv-compliance`. As a rule of thumb, if a dependency is being pulled in specifically for
some kind of test suite, the test rules should live in `//third_party`, where they can depend
on other parts of the tree.

## Third-party Silicon IP

Currently, silicon uses a separate vendoring mechanism: `util/vendor.py`. There are no
concrete plans to migrate off of this script for hardware. This script should not be
used for new software dependencies; instead, use the `//third_party` directory and Bazel
repositories instead.