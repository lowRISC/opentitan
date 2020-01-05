load("@bazel_skylib//lib:unittest.bzl", "analysistest", "asserts")

def _add_manual_tags(attrs):
    if "tags" in attrs and attrs["tags"] != None:
        attrs["tags"] = attrs["tags"] + ["manual"]
    else:
        attrs["tags"] = ["manual"]
    return attrs

def _failure_testing_test_impl(ctx):
    env = analysistest.begin(ctx)
    asserts.expect_failure(env, "This rule should never compile")
    return analysistest.end(env)

failure_testing_test = analysistest.make(
    _failure_testing_test_impl,
    expect_failure = True,
)

def test_cc_library_compilation_failure(**attrs):
    native.cc_library(**_add_manual_tags(attrs))

    target_name = attrs["name"]
    failure_testing_test(
        name = target_name + "_failure_test",
        target_under_test = ":" + target_name,
    )
