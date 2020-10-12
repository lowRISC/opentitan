# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


from collections import OrderedDict
import logging as log
from signal import SIGINT, signal
import threading

from utils import VERBOSE
from Deploy import Deploy, DeployError
from Timer import Timer


class TargetScheduler:
    '''A scheduler for the jobs of a given target'''
    def __init__(self):
        # Sets of items, split up by their current state. The sets are disjoint
        # and their union equals the keys of self.item_to_status.
        self._queued = set()
        self._running = set()
        self._passed = set()
        self._failed = set()
        self._killed = set()

        # A map from the Deploy objects tracked by this class to their current
        # status. This status is 'Q', 'D', 'P', 'F' or 'K', corresponding to
        # membership in the dicts above.
        self.item_to_status = {}

        # A flag set by check_if_done if all jobs are done.
        self._done = True

    def check_status(self):
        '''Return (was_done, is_done, has_started)'''
        was_done = self._done
        self._done = not (self._queued or self._running)
        return (was_done,
                self._done,
                (self._running or self._passed or
                 self._failed or self._killed))

    def print_counters(self, tgt_name, hms):
        total_cnt = len(self.item_to_status)
        width = len(str(total_cnt))

        field_fmt = '{{:0{}d}}'.format(width)
        msg_fmt = ('[Q: {0}, D: {0}, P: {0}, F: {0}, K: {0}, T: {0}]'
                   .format(field_fmt))
        msg = msg_fmt.format(len(self._queued),
                             len(self._running),
                             len(self._passed),
                             len(self._failed),
                             len(self._killed),
                             total_cnt)
        log.info("[%s]: [%s]: %s", hms, tgt_name, msg)

    def add_item(self, item):
        assert item not in self.item_to_status
        self.item_to_status[item] = 'Q'
        self._queued.add(item)
        self._done = False

    def _kill_item(self, item):
        '''Kill a running item'''
        self._running.remove(item)
        item.kill()
        self._killed.add(item)
        self.item_to_status[item] = 'K'

    def dispatch(self, items):
        '''Start (dispatch) each item in the list'''
        for item in items:
            assert item in self._queued
            self._queued.remove(item)
            self._running.add(item)
            self.item_to_status[item] = 'D'
            try:
                item.dispatch_cmd()
            except DeployError as err:
                log.error('{}'.format(err))
                self._kill_item(item)

    def kill(self):
        '''Kill any running items and cancel any that are waiting'''

        # Cancel any waiting items. We take a copy of self._queued to avoid
        # iterating over the set as we modify it.
        for item in [item for item in self._queued]:
            self.cancel(item)

        # Kill any running items. Again, take a copy of the set to avoid
        # modifying it while iterating over it.
        for item in [item for item in self._running]:
            self._kill_item(item)

    def poll(self, hms):
        '''Check for running items that have finished

        Returns True if something changed.

        '''
        to_pass = []
        to_fail = []

        for item in self._running:
            status = item.poll()
            assert status in ['D', 'P', 'F']
            if status == 'D':
                # Still running
                continue
            elif status == 'P':
                log.log(VERBOSE, "[%s]: [%s]: [status] [%s: P]",
                        hms, item.target, item.identifier)
                to_pass.append(item)
            else:
                log.error("[%s]: [%s]: [status] [%s: F]",
                          hms, item.target, item.identifier)
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

    def cancel(self, item):
        '''Cancel an item that is currently queued'''
        assert item in self._queued
        self._queued.remove(item)
        self._killed.add(item)
        self.item_to_status[item] = 'K'


class Scheduler:
    '''An object to run one or more Deploy items'''
    print_legend = True

    # Max jobs running at one time
    max_parallel = 16

    # Max jobs dispatched in one go.
    slot_limit = 20

    def __init__(self, items):
        self.timer = Timer()
        self.queued_items = []
        self.dispatched_items = []

        # An ordered dictionary keyed by target ('build', 'run' or similar).
        # The value for each target is a TargetScheduler object.
        self.schedulers = OrderedDict()

        for item in items:
            self.add_item(item)

    def add_item(self, item):
        '''Add a queued item'''
        self.queued_items.append(item)

        # Like setdefault, but doesn't construct a TargetScheduler object
        # unnecessarily.
        tgt_scheduler = self.schedulers.get(item.target)
        if tgt_scheduler is None:
            tgt_scheduler = TargetScheduler()
            self.schedulers[item.target] = tgt_scheduler

        tgt_scheduler.add_item(item)

    def kill(self):
        '''Kill any running items and cancel any that are waiting'''
        for scheduler in self.schedulers.values():
            scheduler.kill()

    def poll(self):
        '''Update status of running items. Returns true on a change'''
        status_changed = False
        hms = self.timer.hms()
        for scheduler in self.schedulers.values():
            if scheduler.poll(hms):
                status_changed = True

        return status_changed

    def dispatch(self):
        '''Dispatch some queued items if possible'''
        num_slots = min(Scheduler.slot_limit,
                        Scheduler.max_parallel - Deploy.dispatch_counter,
                        len(self.queued_items))
        if not num_slots:
            return

        # We only dispatch things for one target at once.
        cur_tgt = None
        for item in self.dispatched_items:
            if item.process is not None:
                cur_tgt = item.target
                break

        to_dispatch = []

        while len(to_dispatch) < num_slots and self.queued_items:
            next_item = self.queued_items[0]

            # Keep track of the current target to make sure we dispatch things
            # in phases.
            if cur_tgt is None:
                cur_tgt = next_item.target
            if next_item.target != cur_tgt:
                break

            self.queued_items = self.queued_items[1:]

            # Does next_item have any dependencies? Since we dispatch jobs by
            # "target", we can assume that each of those dependencies appears
            # earlier in the list than we do.
            has_failed_dep = False
            for dep in next_item.dependencies:
                dep_status = self.schedulers[dep.target].item_to_status[dep]
                assert dep_status in ['P', 'F', 'K']
                if dep_status in ['F', 'K']:
                    has_failed_dep = True
                    break

            # If has_failed_dep then at least one of the dependencies has been
            # cancelled or has run and failed. Give up on this item too.
            if has_failed_dep:
                self.schedulers[cur_tgt].cancel(next_item)
                continue

            to_dispatch.append(next_item)

        if not to_dispatch:
            return

        assert cur_tgt is not None

        self.dispatched_items.extend(to_dispatch)
        self.schedulers[cur_tgt].dispatch(to_dispatch)

        log.log(VERBOSE, "[%s]: [%s]: [dispatch]:\n%s",
                self.timer.hms(), cur_tgt,
                ", ".join(item.identifier for item in to_dispatch))

    def check_if_done(self, print_status):
        '''Check whether we are finished.

        If print_status or we've reached a time interval then print current
        status for those that weren't known to be finished already.

        '''
        if self.timer.check_time():
            print_status = True

        hms = self.timer.hms()

        all_done = True
        printed_something = False
        for target, scheduler in self.schedulers.items():
            was_done, is_done, has_started = scheduler.check_status()
            all_done &= is_done

            should_print = (print_status and
                            not (was_done and is_done) and
                            (has_started or not printed_something))
            if should_print:
                scheduler.print_counters(target, hms)
                printed_something = True

        return all_done

    def run(self):
        '''Run all items

        Returns a map from item to status.

        '''

        # Print the legend just once (at the start of the first run)
        if Scheduler.print_legend:
            log.info("[legend]: [Q: queued, D: dispatched, "
                     "P: passed, F: failed, K: killed, T: total]")
            Scheduler.print_legend = False

        # Catch one SIGINT and tell the scheduler to quit. On a second, die.
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
            first_time = True
            while True:
                if stop_now.is_set():
                    # We've had an interrupt. Kill any jobs that are running,
                    # then exit.
                    self.kill()
                    exit(1)

                changed = self.poll()
                self.dispatch()
                if self.check_if_done(changed or first_time):
                    break
                first_time = False

                # This is essentially sleep(1) to wait a second between each
                # polling loop. But we do it with a bounded wait on stop_now so
                # that we jump back to the polling loop immediately on a
                # signal.
                stop_now.wait(timeout=1)
        finally:
            signal(SIGINT, old_handler)

        # We got to the end without anything exploding. Extract and return
        # results from the schedulers.
        results = {}
        for scheduler in self.schedulers.values():
            results.update(scheduler.item_to_status)
        return results


def run(items):
    '''Run the given items.

    Returns a map from item to status.

    '''
    return Scheduler(items).run()
