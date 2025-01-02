// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::Bit;
use anyhow::Result;

#[derive(Clone, Debug)]
pub struct PwmPeriod {
    pub period: std::time::Duration,
    pub duty_cycle: f32,
}

pub mod decoder {
    use super::*;

    #[derive(Clone, Debug)]
    struct Sample<const PIN: u8> {
        raw: u8,
    }

    impl<const PIN: u8> Sample<PIN> {
        fn pin(&self) -> Bit {
            ((self.raw >> PIN) & 0x01).into()
        }
    }

    pub struct Decoder<const PIN: u8> {
        pub active_level: Bit,
        pub sampling_period: std::time::Duration,
    }

    impl<const PIN: u8> Decoder<PIN> {
        fn decode_period<I>(&self, samples: &mut I) -> Option<PwmPeriod>
        where
            I: Iterator<Item = Sample<PIN>>,
        {
            let num_active_samples =
                samples.position(|sample| sample.pin() != self.active_level)? + 1;

            let num_inactive_samples =
                samples.position(|sample| sample.pin() == self.active_level)? + 1;

            let period = (num_active_samples + num_inactive_samples) as u32;
            let duty_cycle = num_active_samples as f32 * 100.0 / period as f32;

            Some(PwmPeriod {
                period: period * self.sampling_period,
                duty_cycle,
            })
        }

        pub fn run(&mut self, samples: Vec<u8>) -> Result<Vec<PwmPeriod>> {
            let mut samples = samples.into_iter().map(|raw| Sample::<PIN> { raw });
            // Discard the first period because it may be distorted by initial conditions.
            let _ = self.decode_period(&mut samples);
            let mut pwms = Vec::new();
            while let Some(pwm) = self.decode_period(&mut samples) {
                pwms.push(pwm);
            }
            Ok(pwms)
        }
    }
}
