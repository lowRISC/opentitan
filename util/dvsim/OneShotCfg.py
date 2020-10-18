# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing a one-shot build configuration object
"""

import logging as log
import os
import sys
from collections import OrderedDict

from Deploy import CompileOneShot
from FlowCfg import FlowCfg
from Modes import BuildModes, Modes
from utils import find_and_substitute_wildcards


class OneShotCfg(FlowCfg):
    """Simple one-shot build flow for non-simulation targets like
    linting, synthesis and FPV.
    """
    def __init__(self, flow_cfg_file, proj_root, args):
        super().__init__(flow_cfg_file, proj_root, args)

        assert args.tool is not None

        # Options set from command line
        self.tool = args.tool
        self.verbose = args.verbose
        self.flist_gen_cmd = ""
        self.flist_gen_opts = []
        self.sv_flist_gen_dir = ""
        self.flist_file = ""
        self.build_cmd = ""
        self.build_opts = []
        self.build_log = ""
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
        self.max_msg_count = -1

        # Flow results
        self.result = OrderedDict()
        self.result_summary = OrderedDict()

        self.dry_run = args.dry_run

        # Not needed for this build
        self.verbosity = ""
        self.en_build_modes = []

        # Generated data structures
        self.links = {}
        self.build_list = []
        self.deploy = []
        self.cov = args.cov
        # Parse the cfg_file file tree
        self._parse_flow_cfg(flow_cfg_file)

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

        # Stuff below only pertains to individual cfg (not primary cfg).
        if not self.is_primary_cfg:
            # Print info
            log.info("[scratch_dir]: [%s]: [%s]", self.name, self.scratch_path)

            # Set directories with links for ease of debug / triage.
            self.links = {
                "D": self.scratch_path + "/" + "dispatched",
                "P": self.scratch_path + "/" + "passed",
                "F": self.scratch_path + "/" + "failed",
                "K": self.scratch_path + "/" + "killed"
            }

            # Use the default build mode for tests that do not specify it
            if not hasattr(self, "build_mode"):
                setattr(self, "build_mode", "default")

            # Create objects from raw dicts - build_modes, sim_modes, run_modes,
            # tests and regressions, only if not a primary cfg obj
            self._create_objects()

        # Post init checks
        self.__post_init__()

    def __post_init__(self):
        # Run some post init checks
        super().__post_init__()

    # Purge the output directories. This operates on self.
    def _purge(self):
        if self.scratch_path:
            try:
                log.info("Purging scratch path %s", self.scratch_path)
                os.system("/bin/rm -rf " + self.scratch_path)
            except IOError:
                log.error('Failed to purge scratch directory %s',
                          self.scratch_path)

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

    def _create_dirs(self):
        '''Create initial set of directories
        '''
        # Invoking system calls has a performance penalty.
        # Construct a single command line chained with '&&' to invoke
        # the system call only once, rather than multiple times.
        create_link_dirs_cmd = ""
        for link in self.links.keys():
            create_link_dirs_cmd += "/bin/rm -rf " + self.links[link] + " && "
            create_link_dirs_cmd += "mkdir -p " + self.links[link] + " && "
        create_link_dirs_cmd += " true"

        try:
            os.system(create_link_dirs_cmd)
        except IOError:
            log.error("Error running when running the cmd \"%s\"",
                      create_link_dirs_cmd)
            sys.exit(1)

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
