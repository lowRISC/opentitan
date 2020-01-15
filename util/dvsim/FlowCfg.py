#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""
Class describing a flow configuration object
"""

import logging as log
import pprint

from .utils import *


# Interface class for extensions.
class FlowCfg():
    def __str__(self):
        return pprint.pformat(self.__dict__)

    def __repr__(self):
        return pprint.pformat(self.__dict__)

    def __init__(self, flow_cfg_file, proj_root, args):
        # Options set from command line
        self.flow_cfg_file = flow_cfg_file
        self.proj_root = proj_root
        self.args = args
        self.scratch_root = args.scratch_root

        # Imported cfg files using 'import_cfgs' keyword
        self.imported_cfg_files = []
        self.imported_cfg_files.append(flow_cfg_file)

        # List of cfgs if the parsed cfg is a master cfg list
        self.cfgs = []

        # Add a notion of "master" cfg - this is indicated using
        # a special key 'use_cfgs' within the hjson cfg.
        self.is_master_cfg = False

        # Timestamp
        self.ts_format_long = args.ts_format_long
        self.timestamp_long = args.timestamp_long
        self.ts_format = args.ts_format
        self.timestamp = args.timestamp

    def __post_init__(self):
        # Run some post init checks
        if not self.is_master_cfg:
            # Check if self.cfgs is a list of exactly 1 item (self)
            if not (len(self.cfgs) == 1 and self.cfgs[0].name == self.name):
                log.error("Parse error!\n%s", self.cfgs)
                sys.exit(1)

    @staticmethod
    def create_instance(flow_cfg_file, proj_root, args):
        '''Create a new instance of this class as with given parameters.
        '''
        return FlowCfg(flow_cfg_file, proj_root, args)

    def parse_flow_cfg(self, flow_cfg_file, is_entry_point=True):
        '''
        Parse the flow cfg hjson file. This is a private API used within the
        extended class' __init__ function. This parses the hjson cfg (and
        imports / use cfgs) and builds an initial dictionary.

        This method takes 2 args.
        flow_cfg_file: This is the flow cfg file to be parsed.
        is_entry_point: the cfg file that is passed on the command line is
            the entry point cfg. If the cfg file is a part of an inport_cfgs
            or use_cfgs key, then it is not an entry point.
        '''
        hjson_dict = parse_hjson(flow_cfg_file)

        # Check if this is the master cfg, if this is the entry point cfg file
        if is_entry_point:
            self.is_master_cfg = self.check_if_master_cfg(hjson_dict)

            # If not a master cfg, then register self with self.cfgs
            if self.is_master_cfg is False:
                self.cfgs.append(self)

        # Resolve the raw hjson dict to build this object
        self.resolve_hjson_raw(hjson_dict)

    def check_if_master_cfg(self, hjson_dict):
        # This is a master cfg only if it has a single key called "use_cfgs"
        # which contains a list of actual flow cfgs.
        hjson_cfg_dict_keys = hjson_dict.keys()
        return (len(hjson_cfg_dict_keys) == 1 and \
                "use_cfgs" in hjson_cfg_dict_keys and \
                type(hjson_dict["use_cfgs"]) is list)

    def resolve_hjson_raw(self, hjson_dict):
        attrs = self.__dict__.keys()
        rm_hjson_dict_keys = []
        import_cfgs = []
        use_cfgs = []
        for key in hjson_dict.keys():
            if key in attrs:
                hjson_dict_val = hjson_dict[key]
                self_val = getattr(self, key)
                scalar_types = {str: [""], int: [0, -1], bool: [False]}

                # Case 1: key value in class and hjson_dict differ - error!
                if type(hjson_dict_val) != type(self_val):
                    log.error("Coflicting key types: \"%s\" {\"%s, \"%s\"}",
                              key,
                              type(hjson_dict_val).__name__,
                              type(self_val).__name__)
                    sys.exit(1)

                # Case 2: key value in class and hjson_dict are strs - set if
                # not already set, else error!
                elif type(hjson_dict_val) in scalar_types.keys():
                    defaults = scalar_types[type(hjson_dict_val)]
                    if self_val == hjson_dict_val:
                        rm_hjson_dict_keys.append(key)
                    elif self_val in defaults and not hjson_dict_val in defaults:
                        setattr(self, key, hjson_dict_val)
                        rm_hjson_dict_keys.append(key)
                    elif not self_val in defaults and not hjson_dict_val in defaults:
                        log.error(
                            "Coflicting values {\"%s\", \"%s\"} encountered for key \"%s\"",
                            str(self_val), str(hjson_dict_val), key)
                        sys.exit(1)

                # Case 3: key value in class and hjson_dict are lists - merge'em
                elif type(hjson_dict_val) is list and type(self_val) is list:
                    self_val.extend(hjson_dict_val)
                    setattr(self, key, self_val)
                    rm_hjson_dict_keys.append(key)

                # Case 4: unknown issue
                else:
                    log.error(
                        "Type of \"%s\" (%s) in %s appears to be invalid (should be %s)",
                        key,
                        type(hjson_dict_val).__name__, hjson_dict,
                        type(self_val).__name__)
                    sys.exit(1)

            # If key is 'import_cfgs' then add to the list of cfgs to
            # process
            elif key == 'import_cfgs':
                import_cfgs.extend(hjson_dict[key])
                rm_hjson_dict_keys.append(key)

            # If this is a master cfg list and the key is 'use_cfgs'
            elif self.is_master_cfg and key == "use_cfgs":
                use_cfgs.extend(hjson_dict[key])

            # If this is a not master cfg list and the key is 'use_cfgs'
            elif not self.is_master_cfg and key == "use_cfgs":
                # Throw an error and exit
                log.error(
                    "Key \"use_cfgs\" encountered in a non-master cfg file list \"%s\"",
                    self.flow_cfg_file)
                sys.exit(1)

            else:
                # add key-value to class
                setattr(self, key, hjson_dict[key])
                rm_hjson_dict_keys.append(key)

        # Parse imported cfgs
        for cfg_file in import_cfgs:
            if not cfg_file in self.imported_cfg_files:
                self.imported_cfg_files.append(cfg_file)
                # Substitute wildcards in cfg_file files since we need to process
                # them right away.
                cfg_file = subst_wildcards(cfg_file, self.__dict__)
                self.parse_flow_cfg(cfg_file, False)
            else:
                log.error("Cfg file \"%s\" has already been parsed", cfg_file)

        # Parse master cfg files
        if self.is_master_cfg:
            for cfg_file in use_cfgs:
                # Substitute wildcards in cfg_file files since we need to process
                # them right away.
                cfg_file = subst_wildcards(cfg_file, self.__dict__)
                self.cfgs.append(
                    self.create_instance(cfg_file, self.proj_root, self.args))

    def _process_exports(self):
        # Convert 'exports' to dict
        exports_dict = {}
        if self.exports != []:
            for item in self.exports:
                if type(item) is dict:
                    exports_dict.update(item)
                elif type(item) is str:
                    [key, value] = item.split(':', 1)
                    if type(key) is not str: key = str(key)
                    if type(value) is not str: value = str(value)
                    exports_dict.update({key.strip(): value.strip()})
                else:
                    log.error("Type error in \"exports\": %s", str(item))
                    sys.exit(1)
        self.exports = exports_dict

    def _purge(self):
        '''Purge the existing scratch areas in preperation for the new run.'''
        return

    def purge(self):
        '''Public facing API for _purge().
        '''
        for item in self.cfgs:
            item._purge()

    def _print_list(self):
        '''Print the list of available items that can be kicked off.
        '''
        return

    def print_list(self):
        '''Public facing API for _print_list().
        '''
        for item in self.cfgs:
            item._print_list()

    def _create_deploy_objects(self):
        '''Create deploy objects from items that were passed on for being run.
        The deploy objects for build and run are created from the objects that were
        created from the create_objects() method.
        '''
        return

    def create_deploy_objects(self):
        '''Public facing API for _create_deploy_objects().
        '''
        self.deploy = []
        for item in self.cfgs:
            item._create_deploy_objects()
            self.deploy.extend(item.deploy)

    def _gen_results(self, fmt="md"):
        '''
        The function is called after the flow has executed. It collates the status of
        all run targets and generates a dict. It parses the testplan and maps the generated
        result to the testplan entries to generate a final table (list). It uses the fmt arg
        to dump the final result as a markdown or html.
        '''
        return

    def gen_results(self, fmt="md"):
        '''Public facing API for _gen_results().
        '''
        results = []
        for item in self.cfgs:
            result = item._gen_results(fmt)
            print(result)
            results.append(result)
        return results
