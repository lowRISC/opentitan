# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing a one-shot build configuration object
"""

import logging as log
import os
from collections import OrderedDict

from Deploy import CompileOneShot
from FlowCfg import FlowCfg
from Modes import BuildModes, Modes
from utils import rm_path


class OneShotCfg(FlowCfg):
    """Simple one-shot build flow for non-simulation targets like
    linting, synthesis and FPV.
    """

    ignored_wildcards = (FlowCfg.ignored_wildcards +
                         ['build_mode', 'index', 'test'])

    def __init__(self, flow_cfg_file, hjson_data, args, mk_config):
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

        super().__init__(flow_cfg_file, hjson_data, args, mk_config)

    def _merge_hjson(self, hjson_data):
        # If build_unique is set, then add current timestamp to uniquify it
        if self.build_unique:
            self.build_dir += "_" + self.timestamp

        super()._merge_hjson(hjson_data)

    def _expand(self):
        super()._expand()

        # Stuff below only pertains to individual cfg (not primary cfg).
        if not self.is_primary_cfg and (not self.select_cfgs or
                                        self.name in self.select_cfgs):
            # Print scratch_path at the start:
            log.info("[scratch_path]: [%s] [%s]", self.name, self.scratch_path)

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

    # Purge the output directories. This operates on self.
    def _purge(self):
        assert self.scratch_path
        log.info("Purging scratch path %s", self.scratch_path)
        rm_path(self.scratch_path)

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
        for link in self.links.keys():
            rm_path(self.links[link])
            os.makedirs(self.links[link])

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
