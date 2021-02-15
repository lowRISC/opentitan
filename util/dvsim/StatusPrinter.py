# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import sys

try:
    import enlighten
    ENLIGHTEN_EXISTS = True
except ImportError:
    ENLIGHTEN_EXISTS = False


class StatusPrinter:
    '''Abstraction for printing the current target status onto the console.

    Targets are ASIC tool flow steps such as build, run, cov etc. These steps
    are sequenced by the Scheduler. There may be multiple jobs running in
    parallel in each target. This class provides a mechanism to peridically
    print the completion status of each target onto the terminal. Messages
    printed by this class are rather static in nature - all the necessary
    computations of how the jobs are progressing need to be handled externally.

    The following are the 'fields' accepted by this class:
      hms:    Elapsed time in hh:mm:ss.
      target: The tool flow step.
      msg:    The completion status message (set externally).
      perc:   Percentage of completion.
    '''

    # Print elapsed time in bold.
    hms_fmt = ''.join(['\033[1m', u'{hms:9s}', '\033[0m'])
    header_fmt = hms_fmt + u' [{target:^13s}]: [{msg}]'
    status_fmt = header_fmt + u' {perc:3.0f}%'

    def __init__(self):
        # Once a target is complete, we no longer need to update it - we can
        # just skip it. Maintaining this here provides a way to print the status
        # one last time when it reaches 100%. It is much easier to do that here
        # than in the Scheduler class.
        self.target_done = {}

    def print_header(self, msg):
        '''Initilize / print the header bar.

        The header bar contains an introductory message such as the legend of
        what Q, D, ... mean.'''

        log.info(self.header_fmt.format(hms="", target="legend", msg=msg))

    def init_target(self, target, msg):
        '''Initialize the status bar for each target.'''

        self.target_done[target] = False

    def update_target(self, target, hms, msg, perc):
        '''Periodically update the status bar for each target.'''

        if self.target_done[target]:
            return

        log.info(
            self.status_fmt.format(hms=hms, target=target, msg=msg, perc=perc))
        if perc == 100:
            self.target_done[target] = True

    def exit(self):
        '''Do cleanup activities before exitting.'''

        pass


class EnlightenStatusPrinter(StatusPrinter):
    '''Abstraction for printing status using Enlighten.

    Enlighten is a third party progress bar tool. Documentation:
    https://python-enlighten.readthedocs.io/en/stable/

    Though it offers very fancy progress bar visualization, we stick to a
    simple status bar 'pinned' to the bottom of the screen for each target
    that displays statically, a pre-prepared message. We avoid the progress bar
    visualization since it requires enlighten to perform some computations the
    Scheduler already does. It also helps keep the overhead to a minimum.

    Enlighten does not work if the output of dvsim is redirected to a file, for
    example - it needs to be attached to a TTY enabled stream.
    '''
    def __init__(self):
        super().__init__()

        # Initialize the status_bars for header and the targets .
        self.manager = enlighten.get_manager()
        self.status_header = None
        self.status_target = {}

    def print_header(self, msg):
        self.status_header = self.manager.status_bar(
            status_format=self.header_fmt,
            hms="",
            target="legend",
            msg=
            "Q: queued, D: dispatched, P: passed, F: failed, K: killed, T: total"
        )

    def init_target(self, target, msg):
        super().init_target(target, msg)
        self.status_target[target] = self.manager.status_bar(
            status_format=self.status_fmt,
            hms="",
            target=target,
            msg=msg,
            perc=0.0)

    def update_target(self, target, hms, msg, perc):
        if self.target_done[target]:
            return

        self.status_target[target].update(hms=hms, msg=msg, perc=perc)
        if perc == 100:
            self.target_done[target] = True

    def exit(self):
        self.status_header.close()
        for target in self.status_target:
            self.status_target[target].close()


def get_status_printer():
    """Factory method that returns a status printer instance.

    If ENLIGHTEN_EXISTS (enlighten is installed) and stdout is a TTY, then
    return an instance of EnlightenStatusPrinter, else return an instance of
    StatusPrinter.
    """
    if ENLIGHTEN_EXISTS and sys.stdout.isatty():
        return EnlightenStatusPrinter()
    else:
        return StatusPrinter()
