# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


from collections import OrderedDict
import logging as log
import time

from utils import VERBOSE
from Deploy import Deploy
from Timer import Timer


class TargetStatus:
    '''An object to track the status of a run for a given target'''
    def __init__(self):
        self.counters = OrderedDict()
        self.counters['Q'] = 0
        self.counters['D'] = 0
        self.counters['P'] = 0
        self.counters['F'] = 0
        self.counters['K'] = 0
        self.counters['T'] = 0

        self.done = True

        self.by_item = OrderedDict()

    def add_item(self, item):
        self.by_item[item] = 'Q'
        self.counters['T'] += 1
        self.counters['Q'] += 1
        self.done = False

    def update_item(self, item):
        '''Update the tracked status of the item. Return true on change.'''
        old_status = self.by_item[item]
        if item.status == old_status:
            return False

        self.by_item[item] = item.status

        self.counters[old_status] -= 1
        self.counters[item.status] += 1
        return True

    def check_if_done(self):
        '''Update done flag to match counters. Returns done flag.'''
        self.done = (self.counters['Q'] == 0) and (self.counters['D'] == 0)
        return self.done


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
        # The value for each target is a TargetStatus object.
        self.status = OrderedDict()

        for item in items:
            self.add_item(item)

    def add_item(self, item):
        '''Add a queued item'''
        self.queued_items.append(item)

        # Like setdefault, but doesn't construct a TargetStatus object
        # unnecessarily.
        tgt_status = self.status.get(item.target)
        if tgt_status is None:
            tgt_status = TargetStatus()
            self.status[item.target] = tgt_status

        tgt_status.add_item(item)

    def update_status(self):
        '''Update status of dispatched items. Returns true on a change'''
        status_changed = False
        hms = self.timer.hms()

        # Get status of dispatched items
        for item in self.dispatched_items:
            if item.status == 'D':
                item.get_status()

            tgt_status = self.status[item.target]
            if not tgt_status.update_item(item):
                continue

            status_changed = True
            if item.status == "D":
                continue

            if item.status != "P":
                # Kill its sub items if item did not pass.
                item.set_sub_status("K")
                log.error("[%s]: [%s]: [status] [%s: %s]",
                          hms, item.target, item.identifier, item.status)
            else:
                log.log(VERBOSE, "[%s]: [%s]: [status] [%s: %s]",
                        hms, item.target, item.identifier, item.status)

            # Queue items' sub-items if it is done.
            for sub_item in item.sub:
                self.add_item(sub_item)

        return status_changed

    def dispatch(self):
        '''Dispatch some queued items if possible'''
        num_slots = min(Scheduler.slot_limit,
                        Scheduler.max_parallel - Deploy.dispatch_counter,
                        len(self.queued_items))
        if not num_slots:
            return

        items = self.queued_items[0:num_slots]
        self.queued_items = self.queued_items[num_slots:]
        self.dispatched_items.extend(items)

        tgt_names = OrderedDict()
        for item in items:
            if item.status is None:
                tgt_names.setdefault(item.target, []).append(item.identifier)
                item.dispatch_cmd()

        hms = self.timer.hms()
        for target, names in tgt_names.items():
            log.log(VERBOSE, "[%s]: [%s]: [dispatch]:\n%s",
                    hms, target, ", ".join(names))

    def check_if_done(self, print_status):
        '''Update the "done" flag for each TargetStatus object

        If print_status or we've reached a time interval then print current
        status for those that weren't known to be finished already.

        '''
        if self.timer.check_time():
            print_status = True

        hms = self.timer.hms()

        all_done = True
        for target, tgt_status in self.status.items():
            was_done = tgt_status.done
            tgt_status.check_if_done()
            is_done = tgt_status.done

            all_done &= is_done

            if print_status and not (was_done and is_done):
                stats = tgt_status.counters
                width = "0{}d".format(len(str(stats["T"])))
                msg = "["
                for s in stats.keys():
                    msg += s + ": {:{}}, ".format(stats[s], width)
                msg = msg[:-2] + "]"
                log.info("[%s]: [%s]: %s", hms, target, msg)
        return all_done

    def run(self):
        '''Run all items'''

        # Print the legend just once (at the start of the first run)
        if Scheduler.print_legend:
            log.info("[legend]: [Q: queued, D: dispatched, "
                     "P: passed, F: failed, K: killed, T: total]")
            Scheduler.print_legend = False

        first_time = True
        while True:
            changed = self.update_status()
            self.dispatch()
            if self.check_if_done(changed or first_time):
                break
            first_time = False
            time.sleep(1)


def run(items):
    '''Run the given items'''
    Scheduler(items).run()
