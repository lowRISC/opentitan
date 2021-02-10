# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import time


class Timer:
    '''A timer to keep track of how long jobs have been running

    This has a notion of start time (the time when the object was constructed),
    together with a time when the results should next be printed.

    '''

    print_interval = 5

    def __init__(self):
        self.start = time.monotonic()
        self.next_print = self.start + Timer.print_interval
        self.first_print = True

    def period(self):
        '''Return the float time in seconds since start'''
        return time.monotonic() - self.start

    def hms(self):
        '''Get the time since start in hh:mm:ss'''
        period = self.period()
        secs = int(period + 0.5)
        mins = secs // 60
        hours = mins // 60
        return '{:02}:{:02}:{:02}'.format(hours, mins % 60, secs % 60)

    def check_time(self):
        '''Return true if we have passed next_print.

        If so, increment next_print by print_interval unless the result would
        be in the past, in which case set it to the current time plus
        print_interval.

        '''
        now = time.monotonic()

        if self.first_print:
            self.first_print = False
            return True

        if now < self.next_print:
            return False

        self.next_print += Timer.print_interval
        if self.next_print <= now:
            self.next_print = now + Timer.print_interval

        return True
