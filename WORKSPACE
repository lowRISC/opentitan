load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# bazel_embedded has rules that support building for embedded targets.
# We maintain a fork to build for RiscV32i

git_repository(
    name = "bazel_embedded",
    commit = "b4faaec60b07b11fe3d1fc6b40f22baf31a54690",
    remote = "https://github.com/lowRISC/bazel-embedded.git",
    shallow_since = "1639417565 -0800",
)

load("@bazel_embedded//:bazel_embedded_deps.bzl", "bazel_embedded_deps")

bazel_embedded_deps()

load("@bazel_embedded//platforms:execution_platforms.bzl", "register_platforms")

register_platforms()

load(
    "@bazel_embedded//toolchains/compilers/lowrisc_toolchain_rv32imc:lowrisc_toolchain_rv32imc_repository.bzl",
    "lowrisc_toolchain_rv32imc_compiler",
)

lowrisc_toolchain_rv32imc_compiler()

load(
    "@bazel_embedded//toolchains/lowrisc_toolchain_rv32imc:lowrisc_toolchain_rv32imc.bzl",
    "register_lowrisc_toolchain_rv32imc_toolchain",
)

register_lowrisc_toolchain_rv32imc_toolchain()

# We have a 'vendored' copy of the googletest repo in our repository.
# In the future, we may want to change this to a git repo or http archive.
local_repository(
    name = "googletest",
    path = "sw/vendor/google_googletest",
)

# We have a 'vendored' copy of the google_verible_verilog_syntax_py repo
local_repository(
    name = "google_verible_verilog_syntax_py",
    path = "hw/ip/prim/util/vendor/google_verible_verilog_syntax_py",
)

# Abseil is required by googletest.
http_archive(
    name = "com_google_absl",
    strip_prefix = "abseil-cpp-master",
    urls = ["https://github.com/abseil/abseil-cpp/archive/master.zip"],
)

# Buildifier is a linting tool for our WORKSPACE and BUILD files
http_archive(
    name = "io_bazel_rules_go",
    sha256 = "d1ffd055969c8f8d431e2d439813e42326961d0942bdf734d2c95dc30c369566",
    urls = [
        "https://github.com/bazelbuild/rules_go/releases/download/v0.24.5/rules_go-v0.24.5.tar.gz",
    ],
)

load("@io_bazel_rules_go//go:deps.bzl", "go_register_toolchains", "go_rules_dependencies")

go_rules_dependencies()

go_register_toolchains()

http_archive(
    name = "bazel_gazelle",
    sha256 = "b85f48fa105c4403326e9525ad2b2cc437babaa6e15a3fc0b1dbab0ab064bc7c",
    urls = [
        "https://github.com/bazelbuild/bazel-gazelle/releases/download/v0.22.2/bazel-gazelle-v0.22.2.tar.gz",
    ],
)

load("@bazel_gazelle//:deps.bzl", "gazelle_dependencies")

gazelle_dependencies()

http_archive(
    name = "com_google_protobuf",
    strip_prefix = "protobuf-master",
    urls = ["https://github.com/protocolbuffers/protobuf/archive/master.zip"],
)

load("@com_google_protobuf//:protobuf_deps.bzl", "protobuf_deps")

protobuf_deps()

http_archive(
    name = "com_github_bazelbuild_buildtools",
    strip_prefix = "buildtools-main",
    url = "https://github.com/bazelbuild/buildtools/archive/main.zip",
)

http_archive(
    name = "rules_rust",
    sha256 = "531bdd470728b61ce41cf7604dc4f9a115983e455d46ac1d0c1632f613ab9fc3",
    strip_prefix = "rules_rust-d8238877c0e552639d3e057aadd6bfcf37592408",
    urls = [
        # `main` branch as of 2021-08-23
        "https://github.com/bazelbuild/rules_rust/archive/d8238877c0e552639d3e057aadd6bfcf37592408.tar.gz",
    ],
)

load("@rules_rust//rust:repositories.bzl", "rust_repositories")

rust_repositories(
    edition = "2018",
    version = "1.58.0",
)

load("//third_party/cargo:crates.bzl", "raze_fetch_remote_crates")

raze_fetch_remote_crates()

# boringssl `main-with-bazel` branch as of 2021-11-09.
git_repository(
    name = "boringssl",
    commit = "4fb158925f7753d80fb858cb0239dff893ef9f15",
    remote = "https://boringssl.googlesource.com/boringssl",
)

git_repository(
    name = "mundane",
    commit = "f516499751b45969ac5a95091b1f68cf5ec23f04",
    patch_args = ["-p1"],
    patches = ["//sw/vendor/patches/mundane:build_with_bazel.patch"],
    remote = "https://fuchsia.googlesource.com/mundane",
)
