load("//toolchains/features/common:types.bzl", "CC_ALL_COMMON_FEATURES_INFO")
load("//toolchains/features/embedded:type.bzl", "CC_ALL_EMBEDDED_FEATURES_INFO")

def _print_all_features_impl(ctx):
    common_features = CC_ALL_COMMON_FEATURES_INFO.keys()
    common_features.remove("type_name")
    common_features_str = "Common Features:\n  " + "\n  ".join(common_features)
    embedded_features = CC_ALL_EMBEDDED_FEATURES_INFO.keys()
    embedded_features.remove("type_name")
    embedded_features_str = "Embedded Features:\n  " + "\n  ".join(embedded_features)
    all_feature_str = common_features_str + "\n" + embedded_features_str
    print_script_str = """
echo "{}"
""".format(all_feature_str)
    script = ctx.actions.declare_file("%s.sh" % ctx.label.name)
    ctx.actions.write(script, print_script_str, is_executable = True)
    return [DefaultInfo(executable = script)]

print_all_features = rule(
    _print_all_features_impl,
    executable = True,
)
