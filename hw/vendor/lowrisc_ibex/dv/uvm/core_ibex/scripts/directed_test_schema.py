#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Define a pydantic-schema for specifying directed tests."""

import sys
import pydantic
import pathlib3x as pathlib
from typing import List, Any

import scripts_lib

import logging
logger = logging.getLogger(__name__)


def make_valid_pathlib_path(cls, v: Any) -> pathlib.Path:
    """Pre-converter to ensure input can be converted to a Path."""
    if isinstance(v, pathlib.Path):
        return v
    try:
        return pathlib.Path(v)
    except TypeError:
        raise ValueError(f"Could not convert input ({v}) to valid Path")


def validate_path_exists(v: pathlib.Path, dt: pathlib.Path) -> pathlib.Path:
    """Validatate that a path object exists, relative to a common file (dt)."""
    p = pathlib.Path(dt).parent/v
    if not p.exists():
        raise ValueError(f"Path object does not exist on disk : {p}")
    return p


class DConfig(pydantic.BaseModel):  # noqa
    """Represent a common configuration for building directed tests.

    This object contains information that one or more tests will require
    to build, in a way that encourages reuse of common code.
    """
    class Config:  # noqa
        arbitrary_types_allowed = True

    ##################################
    # DConfig.FIELDS #
    ##################################
    config: str  # name of config (each DTest __must__ specify this too)

    # RTL Simulation Options
    rtl_test: str
    rtl_params: dict
    timeout_s: pydantic.conint(gt=0)

    # Directed Test Build Options
    gcc_opts: str  # any options that don't specify a path eg. "-O3 -g -static"
    ld_script: pathlib.Path  # -T<path>
    includes: pathlib.Path  # -I<path>

    ##################################
    # DConfig.VALIDATORS #
    ##################################

    @pydantic.field_validator('ld_script', 'includes', mode='before')
    @classmethod
    def _make_valid_paths(cls, v: Any) -> pathlib.Path:
        return make_valid_pathlib_path(cls, v)


class DTest(DConfig):  # noqa
    """Represent a entry for a single directed test.

    Each directed test (DTest) inherits from a directed config (DConfig), which can
    specify how the test's sources are built into a testcase. The inheritance
    structure allows multiple tests to inherit common configuration from a single
    config item, reusing the fields and reducing code duplication.
    """
    class Config:  # noqa
        arbitrary_types_allowed = True

    ##################################
    # DTest.FIELDS #
    ##################################
    test: str
    desc: str
    test_srcs: pathlib.Path
    iterations: pydantic.conint(gt=0)

    ##################################
    # DTest.VALIDATORS
    ##################################

    @pydantic.validator('test_srcs', pre=True)
    def _make_valid_paths(cls, v: Any) -> pathlib.Path:
        return make_valid_pathlib_path(cls, v)


class DirectedTestsYaml(pydantic.BaseModel):  # noqa
    """Represent the schema for the <directed-tests>.yaml file.

    The file on-disk should be of the form...
    - A flat list of both DConfig and DTest items
    - Each DTest must specify an existing DConfig item with the key 'config'

    Note that on-disk representation of this file is slightly-different to
    the validation schema defined here, and as part of the validation process
    (see import_model()) we need to account for this.
    """
    class Config:  # noqa
        arbitrary_types_allowed = True

    yaml: pathlib.Path  # Represents the <directed-tests>.yaml config file
    configs: List[DConfig]
    tests: List[DTest]

    @pydantic.validator('yaml')
    def yaml_file_must_exist(cls, v: pathlib.Path):
        """Check that the yaml file exists on disk.

        This field needs its own validator, as other files are checked
        relative to the yaml file.
        """
        if not v.exists():
            raise ValueError(f"Path object not found in filesystem : {v}")
        return v

    @pydantic.model_validator(mode='after')
    def test_config_must_exist(self):
        """A test may only specify common configs in the available list."""
        config_names = {c.config for c in self.configs}
        for test in self.tests:
            if test.config not in config_names:
                raise ValueError(
                    f"Test '{test.test}' gave the config '{test.config}', but "
                    "this config does not exist in the file "
                    f"'{self.yaml}'. Configs detected : {self.configs} \n")
        return self

    @pydantic.model_validator(mode='after')
    def all_paths_must_exist(self):
        """Check that all fields specifying files exist on disk.

        We need to check all fields recursively for pathlib.Path fields,
        then ensure that those files exist, relative to the yaml file.
        """

        def check_model_path_fields_exist(model):
            for k, f in model.__fields__.items():
                if f.annotation != pathlib.Path:
                    continue

                p = validate_path_exists(getattr(model, k), self.yaml)
                setattr(model, k, p)

        for c in self.configs:
            check_model_path_fields_exist(c)

        for t in self.tests:
            check_model_path_fields_exist(t)

        return self


def import_model(directed_test_yaml: pathlib.Path) -> dict:
    """Import and validate data against the model schema, return data as dict.

    If validation errors occur, print them and exit immediately.

    EXAMPLE VALIDATION ERROR

      ERROR:directed_test_schema:
      ################################################################################

      The following errors were encountered while validating :
      --------------------------------------------------------------------------------

      2 validation errors for DirectedTestsYaml
      configs -> 1 -> rtl_test
        field required (type=value_error.missing)
      tests -> 0 -> iterations
         ensure this value is greater than 0 (type=value_error.number.not_gt; limit_value=0)

      ################################################################################

    MEANING
    --> The config entry at index 1 (2nd in the file) is missing the key 'rtl_test'
    --> The test entry at index 0 (1st in the file) has a 'iterations' value that is not >0

    TODO print file/linenum for each validation error
    https://github.com/pydantic/pydantic/issues/1273

    """
    yaml_data = scripts_lib.read_yaml(directed_test_yaml)

    tests = []
    configs = list(filter((lambda i: i.get('test') is None), yaml_data))
    for t in filter((lambda i: i.get('test') is not None), yaml_data):
        # For each test, get the matching config and join the sets together.
        # This works because DTest inherits from DConfig.
        try:
            t_config = next(filter(
                lambda i: i.get('config') == t.get('config'), configs))
        except StopIteration:
            raise ValueError(
                f"Test '{t['test']}' gave the config '{t['config']}', but "
                "this config does not exist in the file "
                f"'{directed_test_yaml}'.\n")
        tests.append({**t_config, **t})
    try:
        m = DirectedTestsYaml(
            yaml=directed_test_yaml,
            configs=configs,
            tests=tests)
    except pydantic.ValidationError as e:
        hl = 80*"#" + "\n"  # hash-line
        dl = 80*"-" + "\n"  # dash-line
        logger.error(f"\n{hl}\n"
                      "The following errors were encountered while validating :"
                     f"\n{dl}\n{e}\n\n{hl}")
        sys.exit(1)

    return m.dict()
