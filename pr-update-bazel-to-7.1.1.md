# Update Bazel to 7.3.1

This PR updates bazel by one major version to 7.3.1. Bzlmod is enabled by
default but OpenTitan does not yet support it, so we opt out.

The `--distdir` flag we were using for airgapped builds has also changed,
so the whole airgapped setup is updated.

`rules_cc` also had to be updated since the version we were using was
incompatible with Bazel 7.3.1.
