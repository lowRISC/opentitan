// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This tool collects code coverage data for OpenTitan FPGA profiles.
//!
//! By taking advantage of Bazel C++ code coverage collection, this script is
//! able to be executed by the existing coverage collection mechanics.
//!
//! Bazel uses the lcov tool for gathering coverage data. There is also
//! an experimental support for clang llvm coverage, which uses the .profraw
//! data files to compute the coverage report.
//!
//! This tool assumes the following environment variables are set:
//! - `ROOT`: Location from where the code coverage collection was invoked.
//! - `RUNFILES_DIR`: Location of the test's runfiles.
//! - `VERBOSE_COVERAGE`: Print debug info from the coverage scripts
//! - `COVERAGE_DIR`: The directory where coverage artifacts are stored.
//! - `TEST_UNDECLARED_OUTPUTS_DIR`: The directory where extra coverage report is stored.
//!
//! The script looks in $COVERAGE_DIR for the OpenTitan compressed counters
//! (`.xprofraw`) and uses lcov to get the coverage data. The coverage data
//! is placed in $COVERAGE_DIR with `.dat` extension.

use anyhow::Result;
use clap::Parser;
use std::env;
use std::fs;

use coverage_lib::{
    debug_environ, debug_log, llvm_cov_export, llvm_profdata_merge, search_by_extension,
    ProfileCounter, ProfileRegistry,
};

#[derive(Debug, Parser)]
#[command(
    name = "collect-cc-coverage",
    about = "Collects On-Device C++ code coverage data"
)]
struct Opts {
    /// Directory where coverage artifacts are stored.
    #[arg(long, env = "COVERAGE_DIR")]
    coverage_dir: Option<std::path::PathBuf>,

    /// Directory where the elf files are stored.
    #[arg(long)]
    elf_dir: Option<std::path::PathBuf>,

    /// Directory where extra coverage report is stored.
    #[arg(long, env = "TEST_UNDECLARED_OUTPUTS_DIR")]
    output_dir: Option<std::path::PathBuf>,
}

fn main() -> Result<()> {
    debug_environ();

    let opts = Opts::parse();
    let coverage_dir = opts.coverage_dir.unwrap();
    let profile_registry = match opts.elf_dir {
        Some(elf_dir) => ProfileRegistry::load_from_dir(&elf_dir),
        None => ProfileRegistry::load_from_runfiles(),
    }?;

    let xprofraw_files = search_by_extension(&coverage_dir, "xprofraw");
    debug_log!("xprofraw_files: {:?}", xprofraw_files);

    // Correlate profile data with counters from the device.
    for path in &xprofraw_files {
        debug_log!("Processing {path:?}");
        // We use .xprofdata instead of .profdata to avoid lcov_merger from parsing it.
        let profdata_file = path.with_extension("xprofdata");
        let profraw_file = path.with_extension("profraw");
        let lcov_file = path.with_extension("dat");

        let counter = ProfileCounter::load(path).unwrap();
        let profile = profile_registry.get(&counter.build_id).unwrap();

        eprintln!("Profile:");
        eprintln!("  Profraw:  {:?}", path);
        eprintln!("  BuildID:  {}", &profile.build_id);
        eprintln!("  Firmware: {:?}", &profile.file_name);
        debug_log!("{:?}", &profile.elf);

        profile.generate_profraw(&counter, &profraw_file).unwrap();
        llvm_profdata_merge(&profraw_file, &profdata_file);
        llvm_cov_export("lcov", &profdata_file, &profile.elf, &lcov_file);

        if let Some(ref output_dir) = opts.output_dir {
            let output_lcov_file = output_dir.join(lcov_file.file_name().unwrap());
            fs::copy(&lcov_file, &output_lcov_file)?;
        }
    }

    debug_log!("Success!");
    Ok(())
}
