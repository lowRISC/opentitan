// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! A simple alarm implementation to display a binary counter over GPIO.

use tock::kernel;

use core::cell::Cell;
use kernel::hil::time::{Alarm, AlarmClient, Frequency};
use kernel::debug;

pub struct CounterAlarm<'a, A: Alarm<'a>> {
    alarm: &'a A,
    /// The current count of the counter
    count: Cell<u32>,
    /// How frequently, in ms, to increment the counter
    interval: Cell<u32>,
    /// The pins to toggle in order
    count_pins: &'a [usize],
    /// Optional text to display over the UART
    splash_text: &'a [&'a str],
    /// A counter for lines of the optional text sent
    splash_count: Cell<u32>,
}

fn ms_to_tick<'a, A: Alarm<'a>>(ms: u32) -> u32 {
    let freq = <A::Frequency>::frequency() as u64;
    let tick = freq * (ms as u64);

    (tick / 1000) as u32
}

impl<'a, A: Alarm<'a>> CounterAlarm<'a, A> {
    pub fn new(alarm: &'a A, pins: &'a [usize]) -> CounterAlarm<'a, A> {
        CounterAlarm {
            alarm: alarm,
            count: Cell::new(0),
            interval: Cell::new(0),
            count_pins: pins,
            splash_text: &[],
            splash_count: Cell::new(0),
        }
    }

    pub fn add_splash_text(&mut self, splash: &'a[&'a str]) {
        self.splash_text = splash;
    }

    pub fn run(&self, interval_ms: u32) {
        self.interval.set(ms_to_tick::<A>(interval_ms));
        let next_trigger = self.alarm.now().wrapping_add(self.interval.get());
        self.alarm.set_alarm(next_trigger);
    }
}

impl<'a, A: Alarm<'a>> AlarmClient for CounterAlarm<'a, A> {
    fn fired(&self) {
        let mut count = self.count.get();

        // Toggle GPIO pins for each bit in count
        for pin in self.count_pins {
            unsafe {
                if count & 1 != 0 {
                    kernel::hil::gpio::Pin::set(&earlgrey::gpio::PORT[*pin])
                } else {
                    kernel::hil::gpio::Pin::clear(&earlgrey::gpio::PORT[*pin])
                }
            }
            count >>= 1;
        }

        let mut splash_count = self.splash_count.get() as usize;
        if self.splash_text.len() > 0 {
            debug!("{}", self.splash_text[splash_count as usize]);
            splash_count += 1;
            if splash_count >= self.splash_text.len() {
                splash_count = 0;
            }
            self.splash_count.set(splash_count as u32);
        }

        // Reset the counter if there were any overflow bits
        if count > 0 {
            self.count.set(1);
        } else {
            self.count.set(self.count.get() + 1);
        }

        let next_trigger = self.alarm.now().wrapping_add(self.interval.get());

        self.alarm.set_alarm(next_trigger);
    }
}
