// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Instant;

use cert_lib::EndorsedCert;
use indexmap::IndexMap;
use ot_hal::dif::lc_ctrl::DifLcCtrlState;
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Stat {
    Microseconds(u64),
    String(String),
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct Statistics(IndexMap<String, Stat>);

#[derive(Clone, Debug, Serialize, Default)]
pub struct DevSeedResponse {
    pub number: usize,
    pub seed: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct LcStateSequence {
    pub initial: DifLcCtrlState,
    pub unlocked: DifLcCtrlState,
    pub individualize: Option<DifLcCtrlState>,
    pub mission_mode: Option<DifLcCtrlState>,
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct PersonalizeResponse {
    pub lc_state: LcStateSequence,
    pub device_id: String,
    pub rma_unlock_token: String,
    pub seeds: DevSeedResponse,
    pub certs: IndexMap<String, EndorsedCert>,
    pub stats: Statistics,
}

impl Statistics {
    pub fn log_elapsed_time(&mut self, name: &str, start: Instant) {
        let end = Instant::now();
        let duration = end - start;
        self.0
            .insert(name.into(), Stat::Microseconds(duration.as_micros() as u64));
    }

    pub fn log_string(&mut self, name: &str, val: &str) {
        self.0.insert(name.into(), Stat::String(val.into()));
    }
}
