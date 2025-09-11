// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module provides utilities to handle coverage profiles for OpenTitan.
//!
//! This module assumes the following environment variables are set:
//! - `ROOT`: Location from where the code coverage collection was invoked.
//! - `RUNFILES_DIR`: Location of the test's runfiles.
//! - `VERBOSE_COVERAGE`: Print debug info from the coverage scripts

use anyhow::{bail, Context, Result};
use byteorder::{LittleEndian, ReadBytesExt};
use object::{Object, ObjectSection};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::io::{Read, Seek, Write};
use std::path::PathBuf;
use std::process;
use zerocopy::{Immutable, IntoBytes};

/// Size of SHA-1 build id.
pub const BUILD_ID_SIZE: usize = 20;
/// LLVM's INSTR_PROF_RAW_MAGIC_32.
/// https://github.com/llvm/llvm-project/blob/llvmorg-16.0.2/compiler-rt/include/profile/InstrProfData.inc#L635-L647
pub const PRF_MAGIC: u64 = 0xff6c70726f665281; // File magic: \x81Rforpl\xff
/// OpenTitan specific compressed counter format.
pub const OTC_MAGIC: u64 = 0xff65766f43544f81; // File magic: \x81OTCove\xff
/// LLVM's INSTR_PROF_RAW_VERSION.
/// https://github.com/llvm/llvm-project/blob/llvmorg-16.0.2/compiler-rt/include/profile/InstrProfData.inc#L649-L651
pub const PRF_VERSION: u64 = 8;
/// LLVM's VARIANT_MASK_BYTE_COVERAGE.
/// https://github.com/llvm/llvm-project/blob/llvmorg-16.0.2/compiler-rt/include/profile/InstrProfData.inc#L673
pub const VARIANT_MASK_BYTE_COVERAGE: u64 = 0x1 << 60;
/// Size of each entry in __llvm_prf_data section.
pub const PRF_DATA_ENTRY_SIZE: u64 = 40;

#[macro_export]
macro_rules! debug_log {
    ($($arg:tt)*) => {
        if env::var("VERBOSE_COVERAGE").is_ok() {
            eprintln!($($arg)*);
        }
    };
}

/// Prints out environment variables to stderr if `VERBOSE_COVERAGE` is set.
///
/// This function is primarily used for debugging purposes, providing visibility
/// into the environment variables to debug bazel integration.
pub fn debug_environ() {
    debug_log!("Environment variables::");
    for (key, value) in env::vars() {
        debug_log!("{}={}", key, value);
    }
}

/// Retrieves a `PathBuf` from an environment variable, panicking if it's empty.
pub fn path_from_env(name: &str) -> PathBuf {
    let path = PathBuf::from(env::var(name).unwrap());
    if path.as_os_str().is_empty() {
        panic!("Environment variable `{name}` cannot be empty.");
    }
    path
}

/// Retrieves the runfiles directory, resolving it to an absolute path.
///
/// This function determines the absolute path to the runfiles directory.
/// It uses the `ROOT` and `RUNFILES_DIR` environment variables. If `RUNFILES_DIR`
/// is not absolute, it's resolved relative to `ROOT`.
pub fn get_runfiles_dir() -> PathBuf {
    let execroot = path_from_env("ROOT");
    let mut runfiles_dir = path_from_env("RUNFILES_DIR");

    if !runfiles_dir.is_absolute() {
        runfiles_dir = execroot.join(runfiles_dir);
    }

    debug_log!("ROOT: {}", execroot.display());
    debug_log!("RUNFILES_DIR: {}", runfiles_dir.display());

    runfiles_dir
}

/// Searches a directory and its subdirectories for files with a specific extension.
///
/// This function recursively traverses the given directory `dir` and all its
/// subdirectories. It collects and returns a vector of `PathBuf` for all
/// files whose extension matches the provided `extension` string.
pub fn search_by_extension(dir: &PathBuf, extension: &str) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                paths.extend(search_by_extension(&path, extension));
            } else if let Some(ext) = path.extension() {
                if ext == extension {
                    paths.push(path);
                }
            }
        }
    }
    paths
}

/// LLVM profraw file header.
///
/// This represents the INSTR_PROF_RAW_HEADER structure defined in:
/// http://github.com/llvm/llvm-project/blob/llvmorg-16.0.2/compiler-rt/include/profile/InstrProfData.inc#L128-L141
#[derive(Debug, Default, Immutable, IntoBytes)]
#[repr(C)]
pub struct ProfileHeader {
    pub magic: u64,
    pub version: u64,
    pub binary_ids_size: u64,
    pub num_data: u64,
    pub padding_bytes_before_counters: u64,
    pub num_counters: u64,
    pub padding_bytes_after_counters: u64,
    pub names_size: u64,
    pub counters_delta: u64,
    pub names_delta: u64,
    pub value_kind_last: u64,
}

/// Represents collected profile counter data from a device.
pub struct ProfileCounter {
    pub build_id: String,
    pub cnts: Vec<u8>,
}

/// Represents coverage metadata from elf files.
pub struct ProfileData {
    pub build_id: String,
    pub elf: PathBuf,
    pub file_name: String,
    pub header: ProfileHeader,
    pub cnts_size: u64,
    pub data: Vec<u8>,
    pub names: Vec<u8>,
}

/// Registry for `ProfileData` instances, indexed by build ID.
///
/// This struct manages a collection of `ProfileData` objects, providing a
/// convenient way to look up coverage metadata by the unique build ID of the
/// ELF file they originate from.
pub struct ProfileRegistry {
    map: HashMap<String, ProfileData>,
}

fn decompress_counters<T: Read>(f: &mut T) -> Result<Vec<u8>> {
    let mut cnts: Vec<u8> = Vec::new();

    let mut byte = [0u8; 1];
    while f.read_exact(&mut byte).is_ok() {
        if byte[0] == 0 || byte[0] == 0xff {
            let tag = byte[0];
            // Compressed padding.
            f.read_exact(&mut byte)?; // Read the padding marker/size.

            // Determine the padding length.
            let pad = match byte[0] {
                0xFE => {
                    let mut pad = [0u8; 2];
                    f.read_exact(&mut pad)?;
                    u16::from_le_bytes(pad) as usize
                }
                0xFF => {
                    let mut pad = [0u8; 4];
                    f.read_exact(&mut pad[..3])?;
                    u32::from_le_bytes(pad) as usize
                }
                // Any other value is the padding length itself.
                _ => byte[0] as usize,
            };
            let new_size = cnts.len() + pad;
            // Prevent excessive counter than what can be held on OpenTitan.
            if new_size > 1024 * 1024 {
                bail!("Decompressed counter is too large");
            }
            cnts.resize(new_size, tag);
        } else {
            // Packed data byte.
            for k in 0..8 {
                let bit = (byte[0] >> k) & 1;
                // If bit is 0, original value is 0xff. Otherwise 0x00.
                cnts.push(if bit == 0 { 0xff } else { 0x00 });
            }
        }
    }

    Ok(cnts)
}

impl ProfileCounter {
    /// Loads `ProfileCounter` from a compressed counter file.
    pub fn load(path: &PathBuf) -> Result<ProfileCounter> {
        let mut f = std::fs::File::open(path)?;

        // Check header
        let magic_bytes = f.read_u64::<LittleEndian>()?;
        if magic_bytes != OTC_MAGIC {
            bail!("Unknown profraw file magic bytes.");
        }

        // Read build id
        let mut build_id = [0u8; BUILD_ID_SIZE];
        f.read_exact(&mut build_id)?;

        // Decompressed cnts
        Ok(ProfileCounter {
            build_id: hex::encode(build_id),
            cnts: decompress_counters(&mut f)?,
        })
    }
}

impl ProfileData {
    /// Creates a `ProfileData` instance by extracting coverage metadata from an ELF file.
    pub fn from_elf(path: &PathBuf) -> Result<ProfileData> {
        let elf = fs::read(path).context("failed to read ELF")?;
        let elf = object::File::parse(&*elf).context("failed to parse ELF")?;
        let file_name = path.file_name().context("Missing filename")?;
        let file_name = file_name.to_str().context("Missing filename")?.to_string();

        let prf_cnts = elf
            .section_by_name("__llvm_prf_cnts")
            .context("__llvm_prf_cnts not found")?;
        let prf_data = elf
            .section_by_name("__llvm_prf_data")
            .context("__llvm_prf_data not found")?;
        let prf_names = elf
            .section_by_name("__llvm_prf_names")
            .context("__llvm_prf_names not found")?;
        let build_id = elf
            .section_by_name(".note.gnu.build-id")
            .context(".note.gnu.build-id not found")?;

        let build_id = build_id.data()?;
        let build_id = &build_id[build_id.len() - BUILD_ID_SIZE..];
        let build_id = hex::encode(build_id);
        debug_log!("Got build_id = {build_id:?}");

        if prf_data.size() % PRF_DATA_ENTRY_SIZE != 0 {
            bail!("Invalid __llvm_prf_data section size");
        }

        Ok(ProfileData {
            build_id,
            elf: path.clone(),
            file_name,
            header: ProfileHeader {
                magic: PRF_MAGIC,
                version: PRF_VERSION | VARIANT_MASK_BYTE_COVERAGE,
                binary_ids_size: 0,
                num_data: prf_data.size() / PRF_DATA_ENTRY_SIZE,
                padding_bytes_before_counters: 0,
                num_counters: 0, // The field will be set later.
                padding_bytes_after_counters: 0,
                names_size: prf_names.size(),
                counters_delta: prf_cnts.address().wrapping_sub(prf_data.address()) as u32 as u64,
                names_delta: prf_names.address() as u32 as u64,
                value_kind_last: 1,
            },
            cnts_size: prf_cnts.size(),
            data: prf_data.data()?.to_vec(),
            names: prf_names.data()?.to_vec(),
        })
    }

    /// Generates a `profraw` file from `ProfileData` and a `ProfileCounter`.
    ///
    /// This function takes a `ProfileData` instance (which contains coverage
    /// metadata from an ELF) and a `ProfileCounter` instance (which contains
    /// the actual counter values from a runtime profile). It combines them to
    /// produce a `profraw` file in the format expected by LLVM's `llvm-profdata`
    /// tool.
    pub fn generate_profraw(&self, counter: &ProfileCounter, output: &PathBuf) -> Result<()> {
        let ProfileCounter { cnts, .. } = counter;

        if self.cnts_size != cnts.len() as u64 {
            bail!("cnts size mismatched");
        }

        let header = ProfileHeader {
            num_counters: cnts.len() as u64,
            ..self.header
        };
        debug_log!("{:#?}", header);
        assert_eq!(
            self.data.len() as u64,
            header.num_data * PRF_DATA_ENTRY_SIZE
        );
        assert_eq!(self.names.len() as u64, header.names_size);

        let mut f = std::fs::File::create(output)?;
        f.write_all(header.as_bytes())?;
        f.write_all(&self.data)?;
        f.write_all(cnts)?;
        f.write_all(&self.names)?;

        let size = f.stream_position()?;
        if size % 8 != 0 {
            let buf = [0; 8];
            let pad: usize = (8 - (size % 8)) as usize;
            f.write_all(&buf[..pad])?;
        }

        Ok(())
    }

    /// Generates a `profraw` file with all counters covered.
    ///
    /// This function creates a synthetic `profraw` file based on the
    /// `ProfileData`, considering all counters as covered.
    pub fn generate_view_profraw(&self, output_path: &PathBuf) -> Result<()> {
        let cnts = vec![0x00; self.cnts_size as usize];
        let counter = ProfileCounter {
            build_id: self.build_id.clone(),
            cnts,
        };
        self.generate_profraw(&counter, output_path)
    }
}

impl ProfileRegistry {
    /// Loads all available `ProfileData` from ELF files found in the runfiles directory
    /// and indexes them by their build ID.
    pub fn load() -> Result<ProfileRegistry> {
        let runfiles_dir = get_runfiles_dir();
        debug_log!("runfiles_dir: {:?}", runfiles_dir);

        // Collect all elf files in the runfiles.
        let elf_files: Vec<PathBuf> = search_by_extension(&runfiles_dir, "elf");

        debug_log!("elf_files: {:?}", elf_files);

        // Index elf profile data with build id.
        let mut profile_map = HashMap::new();
        for path in &elf_files {
            match ProfileData::from_elf(path) {
                Ok(profile) => {
                    debug_log!("Loaded {:?} = {}", profile.file_name, profile.build_id);
                    profile_map.insert(profile.build_id.clone(), profile);
                }
                Err(err) => eprintln!("Skip {path:?}: {err:?}"),
            }
        }
        debug_log!("All elf files are loaded!");

        Ok(ProfileRegistry { map: profile_map })
    }

    /// Returns the `ProfileData` for the given build ID.
    pub fn get(&self, build_id: &str) -> Result<&ProfileData> {
        // Counters only, try to correlate with elf data.
        let profile = match self.map.get(build_id) {
            Some(profile) => profile,
            None => {
                eprintln!("ERROR: Missing profile with build-id {build_id:?}.");
                eprintln!("Loaded elf profiles:");
                for (bid, profile) in &self.map {
                    eprintln!("  {bid} : {:?}", profile.elf);
                }
                bail!("Missing profile with build-id {build_id:?}.");
            }
        };
        Ok(profile)
    }
}

fn find_tool(file_name: &str) -> Result<PathBuf> {
    let path = get_runfiles_dir()
        .join("+lowrisc_rv32imcb_toolchain+lowrisc_rv32imcb_toolchain/bin")
        .join(file_name);
    debug_log!("Testing {file_name} path: {}", path.display());
    if path.exists() {
        return Ok(path);
    }

    bail!("ERROR: missing {file_name} tool.");
}

/// Executes the llvm-profdata tool to merge multiple profraw files into a single profdata file.
///
/// This function constructs and executes an `llvm-profdata merge` command.
///
/// $ llvm-profdata merge \
///     --sparse \
///     "${profraw_file}" \
///     --output "${profdata_file}"
pub fn llvm_profdata_merge(profraw_file: &PathBuf, profdata_file: &PathBuf) {
    let llvm_profdata = find_tool("llvm-profdata").unwrap();

    // "${LLVM_PROFDATA}" merge -output "${profdata_file}" "${profraw_file}"
    let mut llvm_profdata_cmd = process::Command::new(llvm_profdata);
    llvm_profdata_cmd
        .arg("merge")
        .arg("--sparse")
        .arg(profraw_file)
        .arg("--output")
        .arg(profdata_file);

    debug_log!("Spawning {:#?}", llvm_profdata_cmd);
    let status = llvm_profdata_cmd
        .status()
        .expect("Failed to spawn llvm-profdata process");

    if !status.success() {
        process::exit(status.code().unwrap_or(1));
    }
}

/// Executes the llvm-cov tool to export coverage data in a specified format.
///
/// This function constructs and executes an `llvm-cov export` command.
///
/// $ llvm-cov export \
///     -format="${format}" \
///     -instr-profile "${profdata_file}" \
///     -ignore-filename-regex='.*external/.+' \
///     -ignore-filename-regex='^/tmp/.+' \
///     -path-equivalence=.,"${ROOT}" \
///     "${elf}" \
///   | sed 's#/proc/self/cwd/##' > "${output_file}"
pub fn llvm_cov_export(
    format: &str,
    profdata_file: &PathBuf,
    elf: &PathBuf,
    output_file: &PathBuf,
) {
    let execroot = path_from_env("ROOT");
    let llvm_cov = find_tool("llvm-cov").unwrap();

    let mut llvm_cov_cmd = process::Command::new(llvm_cov);
    llvm_cov_cmd
        .arg("export")
        .arg(format!("-format={format}"))
        .arg("-instr-profile")
        .arg(profdata_file)
        .arg("-ignore-filename-regex='.*external/.+'")
        .arg("-ignore-filename-regex='/tmp/.+'")
        .arg(format!("-path-equivalence=.,'{}'", execroot.display()))
        .arg(elf)
        .stdout(process::Stdio::piped());

    debug_log!("Spawning {:#?}", llvm_cov_cmd);
    let child = llvm_cov_cmd
        .spawn()
        .expect("Failed to spawn llvm-cov process");

    let output = child.wait_with_output().expect("llvm-cov process failed");

    // Parse the child process's stdout to a string now that it's complete.
    debug_log!("Parsing llvm-cov output");
    let mut report_str = std::str::from_utf8(&output.stdout)
        .expect("Failed to parse llvm-cov output")
        .replace("/proc/self/cwd/", "")
        .replace(&execroot.display().to_string(), "");

    if format == "lcov" {
        report_str = merge_lcov_count_copies(&report_str).unwrap();
    }

    debug_log!("Writing output to {}", output_file.display());
    fs::write(output_file, report_str).unwrap();
}

/// Merges function and line coverage counts for duplicate entries within a single source file.
///
/// This helper function is used by `merge_lcov_count_copies` to process
/// an individual source file block (`SF:`) from an LCOV report. It aggregates
/// `FNDA:` (function data) and `DA:` (line data) entries, summing up counts
/// for any duplicates.
fn merge_sf_count_copies(contents: &str) -> Result<String> {
    if !contents.starts_with("SF:") {
        bail!("Expected contents to start with SF:, got: {}", contents);
    }

    let mut out = String::new();
    let mut fnda = HashMap::<String, u64>::new();
    let mut da = HashMap::<u64, u64>::new();

    for line in contents.lines() {
        if line.starts_with("FNDA:") {
            // FNDA:<count>,<name>
            let line = line.strip_prefix("FNDA:").unwrap();
            let parts: Vec<&str> = line.split(',').collect();
            let count = parts[0].parse::<u64>()?;
            let name = parts[1].to_string();
            *fnda.entry(name).or_insert(0) += count;
        } else if line.starts_with("DA:") {
            // DA:<lineno>,<count>
            let line = line.strip_prefix("DA:").unwrap();
            let parts: Vec<&str> = line.split(',').collect();
            let lineno = parts[0].parse::<u64>()?;
            let count = parts[1].parse::<u64>()?;
            *da.entry(lineno).or_insert(0) += count;
        } else {
            out.push_str(&format!("{line}\n"));
        }
    }

    // Construct merged FNDA/DA entries
    let mut sorted_fnda: Vec<_> = fnda.into_iter().collect();
    sorted_fnda.sort_by(|a, b| a.0.cmp(&b.0));
    for (name, count) in sorted_fnda {
        out.push_str(&format!("FNDA:{count},{name}\n"));
    }
    let mut sorted_da: Vec<_> = da.into_iter().collect();
    sorted_da.sort_by(|a, b| a.0.cmp(&b.0));
    for (lineno, count) in sorted_da {
        out.push_str(&format!("DA:{lineno},{count}\n"));
    }

    Ok(out)
}

/// Merges function and line coverage counts for each source file within an LCOV report.
///
/// LCOV reports can sometimes contain multiple FNDA entries for the same function in the same
/// source file, and bazel's lcov_merger cannot handle them properly.
///
/// This function processes an entire LCOV report, identifies each `SF:` blocks, and merges all
/// duplicated `FNDA:` (function data) and `DA:` (line data) counts into a single consolidated
/// entry for each source file path.
fn merge_lcov_count_copies(contents: &str) -> Result<String> {
    let mut out = String::new();

    // Iterate through each SF by splitting with end_of_record
    for record in contents.split("\nend_of_record\n") {
        if record.trim().is_empty() {
            continue;
        }

        let record = merge_sf_count_copies(record)?;
        out.push_str(&record);
        out.push_str("end_of_record\n");
    }

    Ok(out)
}
