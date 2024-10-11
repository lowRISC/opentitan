# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Rules to build OpenTitan for the RISC-V target"""

load(
    "@lowrisc_opentitan//rules:rv.bzl",
    _OPENTITAN_CPU = "OPENTITAN_CPU",
    _OPENTITAN_PLATFORM = "OPENTITAN_PLATFORM",
    _opentitan_transition = "opentitan_transition",
)
load(
    "@lowrisc_opentitan//rules/opentitan:cc.bzl",
    _opentitan_binary = "opentitan_binary",
    _opentitan_test = "opentitan_test",
)
load(
    "@lowrisc_opentitan//rules/opentitan:fpga.bzl",
    _fpga_cw305 = "fpga_cw305",
    _fpga_cw310 = "fpga_cw310",
    _fpga_cw340 = "fpga_cw340",
    _fpga_params = "fpga_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:silicon.bzl",
    _silicon = "silicon",
    _silicon_params = "silicon_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:sim_verilator.bzl",
    _sim_verilator = "sim_verilator",
    _verilator_params = "verilator_params",
)
load(
    "@lowrisc_opentitan//rules/opentitan:sim_dv.bzl",
    _dv_params = "dv_params",
    _sim_dv = "sim_dv",
)
load(
    "@lowrisc_opentitan//rules/opentitan:keyutils.bzl",
    _ecdsa_key_by_name = "ecdsa_key_by_name",
    _ecdsa_key_for_lc_state = "ecdsa_key_for_lc_state",
    _rsa_key_by_name = "rsa_key_by_name",
    _rsa_key_for_lc_state = "rsa_key_for_lc_state",
    _spx_key_by_name = "spx_key_by_name",
    _spx_key_for_lc_state = "spx_key_for_lc_state",
)
load(
    "@lowrisc_opentitan//rules/opentitan:ci.bzl",
    "ci_orchestrator",
)
load("@bazel_skylib//lib:sets.bzl", "sets")

# The following definition is used to clear the key set in the signing
# configuration for execution environments (exec_env) and opentitan_test
# and opentitan_binary rules.
CLEAR_KEY_SET = {"//signing:none_key": "none_key"}

# Re-exports of names from transition.bzl; many files in the repo use opentitan.bzl
# to get to them.
OPENTITAN_CPU = _OPENTITAN_CPU
OPENTITAN_PLATFORM = _OPENTITAN_PLATFORM
opentitan_transition = _opentitan_transition

opentitan_binary = _opentitan_binary
fpga_cw305 = _fpga_cw305
fpga_cw310 = _fpga_cw310
fpga_cw340 = _fpga_cw340
fpga_params = _fpga_params

# Temporary export of the old name to prevent merge skew breakage.
cw310_params = _fpga_params

silicon = _silicon
silicon_params = _silicon_params

sim_verilator = _sim_verilator
verilator_params = _verilator_params

sim_dv = _sim_dv
dv_params = _dv_params

ecdsa_key_for_lc_state = _ecdsa_key_for_lc_state
ecdsa_key_by_name = _ecdsa_key_by_name

rsa_key_for_lc_state = _rsa_key_for_lc_state
rsa_key_by_name = _rsa_key_by_name

spx_key_for_lc_state = _spx_key_for_lc_state
spx_key_by_name = _spx_key_by_name

# The default set of test environments for Earlgrey.
EARLGREY_TEST_ENVS = {
    "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
    "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
    "//hw/top_earlgrey:sim_dv": None,
    "//hw/top_earlgrey:sim_verilator": None,
}

# The default set of test environments for Earlgrey.
EARLGREY_SILICON_OWNER_ROM_EXT_ENVS = {
    "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": None,
}

# All CW340 test environments for Earlgrey.
EARLGREY_CW340_TEST_ENVS = {
    "//hw/top_earlgrey:fpga_cw340_test_rom": None,
    "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
    "//hw/top_earlgrey:fpga_cw340_sival": None,
    "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
    "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
}

# Messages we expect for possible test outcomes.
OTTF_SUCCESS_MSG = r"PASS.*\n"
OTTF_FAILURE_MSG = r"(FAIL|FAULT).*\n"
ROM_BOOT_FAILURE_MSG = "BFV:[0-9a-f]{8}"

# These are defined for positive test cases and should be flipped for negative
# test cases, i.e., when a test failure is the expected outcome.
DEFAULT_TEST_SUCCESS_MSG = OTTF_SUCCESS_MSG
DEFAULT_TEST_FAILURE_MSG = "({})|({})".format(
    OTTF_FAILURE_MSG,
    ROM_BOOT_FAILURE_MSG,
)

# Use to clear the default `test_cmd` from any execution environment.
CLEAR_TEST_CMD = " "

def _parameter_name(env, pname):
    if not pname:
        (_, suffix) = env.split(":")
        if "fpga" in suffix:
            pname = "fpga"
        elif "verilator" in suffix:
            pname = "verilator"
        elif "dv" in suffix:
            pname = "dv"
        elif "silicon" in suffix:
            pname = "silicon"
        else:
            fail("Unable to identify parameter block name:", env)
    return pname

def _hacky_tags(env):
    (_, suffix) = env.split(":")
    tags = []
    if suffix.startswith("fpga"):
        tags.append("fpga")

        # We have tags like "cw310_rom_with_real_keys" or "cw310_test_rom"
        # applied to our tests.  Since there is no way to adjust tags in a
        # rule's implementation, we have to infer these tag names from the
        # label name.
        subtag = suffix[5:]
        tags.append(subtag)
        if subtag.startswith("cw305"):
            tags.append("cw305")
        elif subtag.startswith("cw310"):
            tags.append("cw310")
        elif subtag.startswith("hyper310"):
            tags.append("hyper310")
        elif subtag.startswith("cw340"):
            tags.append("cw340")
    if suffix.startswith("silicon"):
        # We add the entire suffix for silicon exec environments to be able
        # to filter tests by them. "silicon_creator" and
        # "silicon_owner_sival_rom_ext" have different target configurations.
        tags.append(suffix)
    return tags

def opentitan_test(
        name,
        srcs = [],
        kind = "flash",
        deps = [],
        copts = [],
        defines = [],
        local_defines = [],
        includes = [],
        linkopts = [],
        linker_script = None,
        ecdsa_key = None,
        rsa_key = None,
        spx_key = None,
        manifest = None,
        exec_env = {},
        fpga = _fpga_params(),
        dv = _dv_params(),
        silicon = _silicon_params(),
        verilator = _verilator_params(),
        data = [],
        run_in_ci = None,
        **kwargs):
    """Instantiate a test per execution environment.

    Args:
      name: The base name of the test.  The name will be extended with the name
            of the execution environment.
      srcs: The source files for this test.
      kind: The kind of test (flash, ram, rom).
      deps: Dependecies for this test.
      copts: Compiler options for this test.
      defines: Compiler defines for this test.
      local_defines: Compiler defines for this test.
      includes: Additional compiler include dirs for this test.
      linker_script: Linker script for this test.
      ecdsa_key: ECDSA key to sign the binary for this test.
      rsa_key: RSA key to sign the binary for this test.
      spx_key: SPX key to sign the binary for this test.
      manifest: manifest used during signing for this test.
      linkopts: Linker options for this test.
      exec_env: A dictionary of execution environments.  The keys are labels to
                execution environments.  The values are the kwargs parameter names
                of the exec_env override or None.  If None, the default parameter
                names of `fpga`, `dv`, `silicon`, or `verilator` will be guessed.
      fpga: Execution overrides for a ChipWhisperer FPGA-based test.
      dv: Execution overrides for a DV-based test.
      silicon: Execution overrides for a silicon-based test.
      verilator: Execution overrides for a verilator-based test.
      run_in_ci: Override the automatic selection of execution environments to run in CI and run exactly those environments.
      kwargs: Additional execution overrides identified by the `exec_env` dict.
    """
    test_parameters = {
        "cw310": fpga,
        "fpga": fpga,
        "dv": dv,
        "silicon": silicon,
        "verilator": verilator,
    }
    test_parameters.update(kwargs)
    kwargs_unused = kwargs.keys()

    # Precompute parameters.
    all_test_params = []
    for (env, pname) in exec_env.items():
        pname = _parameter_name(env, pname)

        # Temporary fallback to "cw310" if "fpga" parameters were not provided.
        # Prevents merge skew problems while the default parameter name changes.
        if pname == "fpga" and pname not in kwargs_unused:
            pname = "cw310"

        extra_tags = _hacky_tags(env)
        tparam = test_parameters[pname]
        if pname in kwargs_unused:
            kwargs_unused.remove(pname)
        all_test_params.append((env, pname, tparam, extra_tags))

    # Find all exec_envs which are not marked as broken.
    non_broken_exec_env = []
    for (env, pname, tparam, extra_tags) in all_test_params:
        if not ("broken" in tparam.tags + extra_tags):
            non_broken_exec_env.append(env)

    if run_in_ci == None:
        skip_in_ci = sets.make(ci_orchestrator(name, non_broken_exec_env))
        all_envs = sets.make([env for (env, _, _, _) in all_test_params])
        run_in_ci = sets.difference(all_envs, skip_in_ci)
    else:
        run_in_ci = sets.make(run_in_ci)

    all_tests = []
    for (env, pname, tparam, extra_tags) in all_test_params:
        # Tag test if it must not run in CI.
        skip_in_ci = []
        if not sets.contains(run_in_ci, env):
            skip_in_ci.append("skip_in_ci")

        (_, suffix) = env.split(":")
        test_name = "{}_{}".format(name, suffix)
        all_tests.append(":" + test_name)
        _opentitan_test(
            name = test_name,
            srcs = srcs,
            kind = kind,
            deps = deps,
            copts = copts,
            defines = defines + getattr(tparam, "defines", []),
            local_defines = local_defines,
            includes = includes,
            linker_script = linker_script,
            linkopts = linkopts,
            exec_env = env,
            naming_convention = "{name}",
            # Tagging and timeout info always comes from a param block.
            tags = tparam.tags + extra_tags + skip_in_ci,
            timeout = tparam.timeout,
            local = tparam.local,
            # Override parameters in the test rule.
            test_harness = tparam.test_harness,
            binaries = tparam.binaries,
            rom = tparam.rom,
            rom_ext = tparam.rom_ext,
            otp = tparam.otp,
            bitstream = tparam.bitstream,
            post_test_cmd = getattr(tparam, "post_test_cmd", ""),
            post_test_harness = getattr(tparam, "post_test_harness", None),
            test_cmd = tparam.test_cmd,
            param = tparam.param,
            data = data + tparam.data,
            ecdsa_key = ecdsa_key,
            rsa_key = rsa_key,
            spx_key = spx_key,
            manifest = manifest,
            needs_jtag = getattr(tparam, "needs_jtag", False),
        )

    # Make sure that we used all elements in kwargs
    if len(kwargs_unused) > 0:
        fail("the following arguments passed to opentitan_test were not used: {}".format(", ".join(kwargs_unused)))

    native.test_suite(
        name = name,
        tests = all_tests,
        tags = ["manual"],
    )
