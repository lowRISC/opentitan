// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

use crate::app::{StagedProgressBar, TransportWrapper};
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
    pub fn init(&self, transport: &TransportWrapper) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(bootstrap) = &self.bootstrap {
            self.load(transport, bootstrap)?;
        }
        Ok(None)
    }

    pub fn load(&self, transport: &TransportWrapper, file: &Path) -> Result<()> {
        let payload = std::fs::read(file)?;
        let progress = StagedProgressBar::new();
        let mut options = self.options.clone();
        if options.clear_uart.is_none() {
            options.clear_uart = Some(true);
        }
        bootstrap::Bootstrap::update_with_progress(transport, &options, &payload, &progress)?;
        Ok(())
    }
}
