# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing a one-shot build configuration object
"""

import logging as log
import sys

from Deploy import *
from FlowCfg import FlowCfg
from Modes import *
from utils import *


class OneShotCfg(FlowCfg):
    """Simple one-shot build flow for non-simulation targets like
    linting, synthesis and FPV.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        super().__init__(flow_cfg_file, proj_root, args)

        # Options set from command line
        self.tool = args.tool
        self.email = args.email
        self.verbose = args.verbose
        self.build_cmd = ""
        self.build_opts = []
        self.report_cmd = ""
        self.report_opts = []
        self.build_opts.extend(args.build_opts)
        self.build_unique = args.build_unique
        self.build_only = args.build_only

        # Options built from cfg_file files
        self.project = ""
        self.flow = ""
        self.flow_makefile = ""
        self.scratch_path = ""
        self.build_dir = ""
        self.run_dir = ""
        self.sw_build_dir = ""
        self.pass_patterns = []
        self.fail_patterns = []
        self.name = ""
        self.dut = ""
        self.fusesoc_core = ""
        self.ral_spec = ""
        self.build_modes = []
        self.run_modes = []
        self.regressions = []

        # Flow results
        self.result = {}
        self.result_summary = {}

        self.dry_run = args.dry_run

        # Not needed for this build
        self.verbosity = ""
        self.en_build_modes = []

        # Generated data structures
        self.build_list = []
        self.deploy = []

        # Parse the cfg_file file tree
        self.parse_flow_cfg(flow_cfg_file)
        self._post_parse_flow_cfg()

        # If build_unique is set, then add current timestamp to uniquify it
        if self.build_unique:
            self.build_dir += "_" + self.timestamp

        # Process overrides before substituting the wildcards.
        self._process_overrides()

        # Make substitutions, while ignoring the following wildcards
        # TODO: Find a way to set these in sim cfg instead
        ignored_wildcards = ["build_mode", "index", "test"]
        self.__dict__ = find_and_substitute_wildcards(self.__dict__,
                                                      self.__dict__,
                                                      ignored_wildcards)

        # Stuff below only pertains to individual cfg (not master cfg).
        if not self.is_master_cfg:
            # Print info
            log.info("[scratch_dir]: [%s]: [%s]", self.name, self.scratch_path)

            # Use the default build mode for tests that do not specify it
            if not hasattr(self, "build_mode"):
                setattr(self, "build_mode", "default")

            self._process_exports()

            # Create objects from raw dicts - build_modes, sim_modes, run_modes,
            # tests and regressions, only if not a master cfg obj
            self._create_objects()

            # Post init checks
            self.__post_init__()

    def __post_init__(self):
        # Run some post init checks
        super().__post_init__()

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return OneShotCfg(flow_cfg_file, proj_root, args)

    def _create_objects(self):
        # Create build and run modes objects
        build_modes = Modes.create_modes(BuildModes,
                                         getattr(self, "build_modes"))
        setattr(self, "build_modes", build_modes)

        # All defined build modes are being built, h
        # ence extend all with the global opts.
        for build_mode in build_modes:
            build_mode.build_opts.extend(self.build_opts)

    def _print_list(self):
        for list_item in self.list_items:
            log.info("---- List of %s in %s ----", list_item, self.name)
            if hasattr(self, list_item):
                items = getattr(self, list_item)
                for item in items:
                    log.info(item)
            else:
                log.error("Item %s does not exist!", list_item)

    def _create_deploy_objects(self):
        '''Create deploy objects from build modes
        '''
        builds = []
        build_map = {}
        for build in self.build_modes:
            item = CompileOneShot(build, self)
            builds.append(item)
            build_map[build] = item

        self.builds = builds
        self.deploy = builds

        # Create initial set of directories before kicking off the regression.
        self._create_dirs()
