// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

use crate::app::{self, TransportWrapper};
use crate::bootstrap::{self, BootstrapOptions};

/// Load a program into the chip.
#[derive(Debug, StructOpt)]
pub struct Bootstrap {
    #[structopt(flatten)]
    pub options: BootstrapOptions,

    #[structopt(long, help = "RV32 test binary to load")]
    pub bootstrap: Option<PathBuf>,
}

impl Bootstrap {
    pub fn init(&self, transport: &TransportWrapper) -> Result<Option<Box<dyn Serialize>>> {
        if let Some(bootstrap) = &self.bootstrap {
            self.load(transport, bootstrap)?;
        }
        Ok(None)
    }

    pub fn load(&self, transport: &TransportWrapper, file: &Path) -> Result<()> {
        let payload = std::fs::read(file)?;
        let progress = app::progress_bar(payload.len() as u64);
        bootstrap::Bootstrap::update_with_progress(
            &transport,
            &self.options,
            &payload,
            |_, chunk| {
                progress.inc(chunk as u64);
            },
        )?;
        Ok(())
    }
}
