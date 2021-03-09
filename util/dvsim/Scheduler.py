# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import threading
from collections import OrderedDict
from signal import SIGINT, signal

from Launcher import LauncherError
from Timer import Timer
from utils import VERBOSE


class TargetScheduler:
    '''A scheduler for the jobs of a given target'''
    def __init__(self, name):
        self.name = name

        # Sets of items, split up by their current state. The sets are disjoint
        # and their union equals the keys of self.item_to_status. _queued is a
        # list so that we dispatch things in order (relevant for things like
        # tests where we have ordered things cleverly to try to see failures
        # early)
        self._queued = []
        self._running = set()
        self._passed = set()
        self._failed = set()
        self._killed = set()

        # A map from the Deploy objects tracked by this class to their current
        # status. This status is 'Q', 'D', 'P', 'F' or 'K', corresponding to
        # membership in the dicts above.
        self.item_to_status = {}

    def add_item(self, item):
        assert item not in self.item_to_status
        assert item not in self._queued
        self.item_to_status[item] = 'Q'
        self._queued.append(item)

    def _kill_item(self, item):
        '''Kill a running item'''
        self._running.remove(item)
        item.launcher.kill()
        self._killed.add(item)
        self.item_to_status[item] = 'K'

    def _poll(self, hms):
        '''Check for running items that have finished.

        Returns True if something changed.
        '''
        to_pass = []
        to_fail = []

        for item in self._running:
            status = item.launcher.poll()
            assert status in ['D', 'P', 'F']
            if status == 'D':
                # Still running
                continue
            elif status == 'P':
                log.log(VERBOSE, "[%s]: [%s]: [status] [%s: P]", hms,
                        item.target, item.full_name)
                to_pass.append(item)
            else:
                log.error("[%s]: [%s]: [status] [%s: F]", hms, item.target,
                          item.full_name)
                to_fail.append(item)

        for item in to_pass:
            self._running.remove(item)
            self._passed.add(item)
            self.item_to_status[item] = 'P'
        for item in to_fail:
            self._running.remove(item)
            self._failed.add(item)
            self.item_to_status[item] = 'F'

        return to_pass or to_fail

    def _dispatch(self, hms, old_results):
        '''Dispatch some queued items if possible.

        See run() for the format of old_results.
        '''
        num_slots = min(Scheduler.slot_limit,
                        Scheduler.max_parallel - len(self._running),
                        len(self._queued))
        if num_slots <= 0:
            return

        to_dispatch = []

        while len(to_dispatch) < num_slots and self._queued:
            next_item = self._queued.pop(0)
            # Does next_item have any dependencies? Since we dispatch jobs by
            # target, we can assume that each of those dependencies appears
            # in old_results.
            has_failed_dep = False
            for dep in next_item.dependencies:
                dep_status = old_results[dep]
                assert dep_status in ['P', 'F', 'K']

                if next_item.needs_all_dependencies_passing:
                    if dep_status in ['F', 'K']:
                        has_failed_dep = True
                        break
                else:
                    # Set has_failed_dep default value to True only if the
                    # next_item has dependencies, and next_item does not require
                    # all dependencies to pass
                    has_failed_dep = True
                    if dep_status in ['P']:
                        has_failed_dep = False
                        break

            # If has_failed_dep then at least one of the dependencies has been
            # cancelled or has run and failed. Give up on this item too.
            if has_failed_dep:
                self._killed.add(next_item)
                self.item_to_status[next_item] = 'K'
                continue

            to_dispatch.append(next_item)

        if not to_dispatch:
            return

        log.log(VERBOSE, "[%s]: [%s]: [dispatch]:\n%s", hms, self.name,
                ", ".join(item.full_name for item in to_dispatch))

        for item in to_dispatch:
            self._running.add(item)
            self.item_to_status[item] = 'D'
            try:
                item.launcher.launch()
            except LauncherError as err:
                log.error('{}'.format(err))
                self._kill_item(item)

    def _kill(self):
        '''Kill any running items and cancel any that are waiting'''

        # Cancel any waiting items. We take a copy of self._queued to avoid
        # iterating over the set as we modify it.
        for item in [item for item in self._queued]:
            self._cancel(item)

        # Kill any running items. Again, take a copy of the set to avoid
        # modifying it while iterating over it.
        for item in [item for item in self._running]:
            self._kill_item(item)

    def _cancel(self, item):
        '''Cancel an item that is currently queued'''
        assert item in self._queued
        self._queued.remove(item)
        self._killed.add(item)
        self.item_to_status[item] = 'K'

    def _check_if_done(self, timer, hms, print_status):
        '''Check whether we are finished.

        If print_status or we've reached a time interval then print current
        status for those jobs that weren't known to be finished already.
        '''
        if timer.check_time():
            print_status = True

        if print_status:
            total_cnt = len(self.item_to_status)
            width = len(str(total_cnt))

            field_fmt = '{{:0{}d}}'.format(width)
            msg_fmt = ('[Q: {0}, D: {0}, P: {0}, F: {0}, K: {0}, T: {0}]'.
                       format(field_fmt))
            msg = msg_fmt.format(len(self._queued), len(self._running),
                                 len(self._passed), len(self._failed),
                                 len(self._killed), total_cnt)
            log.info("[%s]: [%s]: %s", hms, self.name, msg)

        return not (self._queued or self._running)

    def run(self, timer, old_results):
        '''Run the jobs for this target.

        timer is a Timer that was started at the start of the Runner's run.

        old_results is a dictionary mapping items (from previous targets) to
        statuses. Every job that appears as a dependency will be in this list
        (because it ran as part of a previous target).

        Returns the results from this target (in the same format).
        '''
        # Catch one SIGINT and tell the runner to quit. On a second, die.
        stop_now = threading.Event()
        old_handler = None

        def on_sigint(signal_received, frame):
            log.info('Received SIGINT. Exiting gracefully. '
                     'Send another to force immediate quit '
                     '(but you may need to manually kill child processes)')

            # Restore old handler to catch any second signal
            assert old_handler is not None
            signal(SIGINT, old_handler)

            stop_now.set()

        old_handler = signal(SIGINT, on_sigint)

        try:
            while True:
                if stop_now.is_set():
                    # We've had an interrupt. Kill any jobs that are running,
                    # then exit.
                    self._kill()
                    exit(1)

                hms = timer.hms()
                changed = self._poll(hms)
                self._dispatch(hms, old_results)
                if self._check_if_done(timer, hms, changed):
                    break

                # This is essentially sleep(1) to wait a second between each
                # polling loop. But we do it with a bounded wait on stop_now so
                # that we jump back to the polling loop immediately on a
                # signal.
                stop_now.wait(timeout=1)
        finally:
            signal(SIGINT, old_handler)

        # We got to the end without anything exploding. Return the results for our jobs.
        return self.item_to_status


class Scheduler:
    '''An object to run one or more Deploy items'''

    # Max jobs running at one time
    max_parallel = 16

    # Max jobs dispatched in one go.
    slot_limit = 20

    def __init__(self, items):
        # An ordered dictionary keyed by target ('build', 'run' or similar).
        # The value for each target is a TargetScheduler object.
        self.schedulers = OrderedDict()

        for item in items:
            # This works like setdefault, but doesn't construct a TargetScheduler
            # object unnecessarily.
            tgt_scheduler = self.schedulers.get(item.target)
            if tgt_scheduler is None:
                tgt_scheduler = TargetScheduler(item.target)
                self.schedulers[item.target] = tgt_scheduler

            tgt_scheduler.add_item(item)

    def run(self):
        '''Run all items

        Returns a map from item to status.
        '''
        timer = Timer()

        log.info("[legend]: [Q: queued, D: dispatched, "
                 "P: passed, F: failed, K: killed, T: total]")
        results = {}
        for scheduler in self.schedulers.values():
            results.update(scheduler.run(timer, results))
        return results
