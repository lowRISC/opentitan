# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import sys
from typing import List, Optional


class Mode:
    """A collection of options that represents a single mode.

    This might be a run mode (options for an EDA tool?), a build mode, a test
    or a regression.
    """

    def __init__(self, type_name: str, mdict):
        keys = mdict.keys()
        attrs = self.__dict__.keys()

        if 'name' not in keys:
            log.error("Key \"name\" missing in mode %s", mdict)
            sys.exit(1)

        if not hasattr(self, "type"):
            log.fatal("Key \"type\" is missing or invalid")
            sys.exit(1)

        for key in keys:
            if key not in attrs:
                log.error(f"Key {key} in {mdict} is invalid. Supported "
                          f"attributes for a {type_name} are {attrs}")
                sys.exit(1)
            setattr(self, key, mdict[key])

    def get_sub_modes(self):
        return getattr(self, "en_" + self.type + "_modes", [])

    def set_sub_modes(self, sub_modes):
        setattr(self, "en_" + self.type + "_modes", sub_modes)

    def merge_mode(self, mode: 'Mode') -> None:
        '''Update this object by merging it with mode.'''

        sub_modes = self.get_sub_modes()
        is_sub_mode = mode.name in sub_modes

        # If the mode to be merged in is not known as a sub-mode of this mode
        # then something has gone wrong. Generate an error.
        if mode.name != self.name and not is_sub_mode:
            log.error(f"Cannot merge mode {self.name} with {mode.name}: "
                      f"it is not a sub-mode and they are not equal.")
            sys.exit(1)

        # Merge attributes in self with attributes in mode arg, since they are
        # the same mode but set in separate files, or a sub-mode.
        for attr, self_attr_val in self.__dict__.items():
            mode_attr_val = getattr(mode, attr, None)

            # If sub-mode, skip the name: it could differ.
            if is_sub_mode and attr == 'name':
                continue

            # If mode's value is None, then nothing to do here.
            if mode_attr_val is None:
                continue

            # If self value is None, then replace with mode's value.
            if self_attr_val is None:
                setattr(self, attr, mode_attr_val)
                continue

            # If they are equal, then nothing to do here.
            if self_attr_val == mode_attr_val:
                continue

            # Extend if they are both lists.
            if isinstance(self_attr_val, list):
                assert isinstance(mode_attr_val, list)
                self_attr_val.extend(mode_attr_val)
                continue

            # If the current val is default, replace with new.
            scalar_types = {str: "", int: -1}
            default_val = scalar_types.get(type(self_attr_val))

            if type(self_attr_val) in scalar_types.keys(
            ) and self_attr_val == default_val:
                setattr(self, attr, mode_attr_val)
                continue

            # Check if their types are compatible.
            if type(self_attr_val) != type(mode_attr_val):
                log.error(
                    "Mode %s cannot be merged into %s due to a conflict "
                    "(type mismatch): %s: {%s(%s), %s(%s)}", mode.name,
                    self.name, attr, str(self_attr_val),
                    str(type(self_attr_val)), str(mode_attr_val),
                    str(type(mode_attr_val)))
                sys.exit(1)

            # Check if they are different non-default values.
            if self_attr_val != default_val and mode_attr_val != default_val:
                log.error(
                    "Mode %s cannot be merged into %s due to a conflict "
                    "(unable to pick one from different values): "
                    "%s: {%s, %s}", mode.name, self.name, attr,
                    str(self_attr_val), str(mode_attr_val))
                sys.exit(1)

        # Check newly appended sub_modes, remove 'self' and duplicates
        sub_modes = self.get_sub_modes()

        if sub_modes != []:
            new_sub_modes = []
            for sub_mode in sub_modes:
                if self.name != sub_mode and sub_mode not in new_sub_modes:
                    new_sub_modes.append(sub_mode)
            self.set_sub_modes(new_sub_modes)
        return True

    @staticmethod
    def create_modes(ModeType, mdicts):
        '''
        Create modes of type ModeType from a given list of raw dicts
        Process dependencies.
        Return a list of modes objects.
        '''

        def merge_sub_modes(mode, parent, objs):
            # Check if there are modes available to merge
            sub_modes = mode.get_sub_modes()
            if sub_modes == []:
                return

            # Set parent if it is None. If not, check cyclic dependency
            if parent is None:
                parent = mode
            else:
                if mode.name == parent.name:
                    log.error("Cyclic dependency when processing mode \"%s\"",
                              mode.name)
                    sys.exit(1)

            for sub_mode in sub_modes:
                # Find the sub_mode obj from str
                found = False
                for obj in objs:
                    if sub_mode == obj.name:
                        # First recursively merge the sub_modes
                        merge_sub_modes(obj, parent, objs)

                        # Now merge the sub mode with mode
                        mode.merge_mode(obj)
                        found = True
                        break
                if not found:
                    log.error(
                        "Sub mode \"%s\" added to mode \"%s\" was not found!",
                        sub_mode, mode.name)
                    sys.exit(1)

        modes_objs = []
        # create a default mode if available
        default_mode = ModeType.get_default_mode()
        if default_mode is not None:
            modes_objs.append(default_mode)

        # Process list of raw dicts that represent the modes
        # Pass 1: Create unique set of modes by merging modes with the same name
        for mdict in mdicts:
            # Create a new item
            new_mode_merged = False
            new_mode = ModeType(mdict)
            for mode in modes_objs:
                # Merge new one with existing if available
                if mode.name == new_mode.name:
                    mode.merge_mode(new_mode)
                    new_mode_merged = True
                    break

            # Add the new mode to the list if not already appended
            if not new_mode_merged:
                modes_objs.append(new_mode)
                ModeType.item_names.append(new_mode.name)

        # Pass 2: Recursively expand sub modes within parent modes
        for mode in modes_objs:
            merge_sub_modes(mode, None, modes_objs)

        # Return the list of objects
        return modes_objs

    @staticmethod
    def get_default_mode(ModeType):
        return None


def find_mode(mode_name: str, modes: List[Mode]) -> Optional[Mode]:
    '''Search through a list of modes and return the one with the given name.

    Return None if nothing was found.
    '''
    for mode in modes:
        if mode_name == mode.name:
            return mode
    return None


def find_and_merge_modes(mode: Mode,
                         mode_names: List[str],
                         modes: List[Mode],
                         merge_modes: bool = True):
    found_mode_objs = []
    for mode_name in mode_names:
        sub_mode = find_mode(mode_name, modes)
        if sub_mode is not None:
            found_mode_objs.append(sub_mode)
            if merge_modes is True:
                mode.merge_mode(sub_mode)
        else:
            log.error("Mode \"%s\" enabled within mode \"%s\" not found!",
                      mode_name, mode.name)
            sys.exit(1)
    return found_mode_objs


class BuildMode(Mode):
    """
    Build modes.
    """

    # Maintain a list of build_modes str
    item_names = []

    def __init__(self, bdict):
        self.name = ""
        self.type = "build"
        self.is_sim_mode = 0
        self.pre_build_cmds = []
        self.post_build_cmds = []
        self.en_build_modes = []
        self.build_opts = []
        self.build_timeout_mins = None
        self.pre_run_cmds = []
        self.post_run_cmds = []
        self.run_opts = []
        self.sw_images = []
        self.sw_build_opts = []

        super().__init__("build mode", bdict)
        self.en_build_modes = list(set(self.en_build_modes))

    @staticmethod
    def get_default_mode():
        return BuildMode({"name": "default"})


class RunMode(Mode):
    """A collection of options for running a test."""

    # Maintain a list of run_modes str
    item_names = []

    def __init__(self, rdict):
        self.name = ""
        self.type = "run"
        self.reseed = None
        self.pre_run_cmds = []
        self.post_run_cmds = []
        self.en_run_modes = []
        self.run_opts = []
        self.uvm_test = ""
        self.uvm_test_seq = ""
        self.build_mode = ""
        self.run_timeout_mins = None
        self.run_timeout_multiplier = None
        self.sw_images = []
        self.sw_build_device = ""
        self.sw_build_opts = []

        super().__init__("run mode", rdict)
        self.en_run_modes = list(set(self.en_run_modes))

    @staticmethod
    def get_default_mode():
        return None
