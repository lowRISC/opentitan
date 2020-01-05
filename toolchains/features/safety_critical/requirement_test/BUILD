load(":defs.bzl", "test_cc_library_compilation_failure")

SOURCE_FILES = [
    "av_rule_11",
    "av_rule_157",
    "av_rule_187_188",
    "av_rule_193",
    "av_rule_197",
    "av_rule_1",
    "av_rule_203",
    "av_rule_20",
    "av_rule_24",
    "av_rule_9_10",
    "av_rule_135",
    "av_rule_162",
    "av_rule_18",
    "av_rule_194",
    "av_rule_198",
    "av_rule_200",
    "av_rule_204",
    "av_rule_21",
    "av_rule_25",
    "av_rule_13",
    "av_rule_17",
    "av_rule_191",
    "av_rule_195",
    "av_rule_199",
    "av_rule_201",
    "av_rule_206",
    "av_rule_22",
    "av_rule_2",
    "av_rule_14",
    "av_rule_186",
    "av_rule_192",
    "av_rule_196",
    "av_rule_19",
    "av_rule_202",
    "av_rule_208",
    "av_rule_23",
    "av_rule_3",
]

[
    test_cc_library_compilation_failure(
        name = file,
        srcs = [
            file + ".cc",
        ],
    )
    for file in SOURCE_FILES
]
