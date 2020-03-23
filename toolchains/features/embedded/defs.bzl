load("//toolchains/features/embedded/impl:gcc.bzl", "GetGccEmbeddedFeatures")

_IMPL_LOOKUP = {
    "GCC": GetGccEmbeddedFeatures,
}

def GetEmbeddedFeatures(compiler):
    return _IMPL_LOOKUP[compiler]()
