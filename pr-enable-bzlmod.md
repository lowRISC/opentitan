# Enable bzlmod in hybrid mode

Bzlmod is enabled with the `--enable_bzlmod` flag, but all our dependencies
are coming from `WORKSPACE.bzlmod`. These can be gradually ported over to
`MODULE.bazel` one by one and Bazel will use both.
