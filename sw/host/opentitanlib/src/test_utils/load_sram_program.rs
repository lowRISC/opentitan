// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use std::str::FromStr;
use std::time::Duration;

use anyhow::{bail, Context, Result};
use bindgen::sram_program::{SRAM_MAGIC_SP_CRC_ERROR, SRAM_MAGIC_SP_EXECUTION_DONE};
use byteorder::{ByteOrder, LittleEndian, WriteBytesExt};
use crc::Crc;
use object::{Object, ObjectSection, SectionKind};
use serde::{Deserialize, Serialize};
use structopt::StructOpt;
use thiserror::Error;

use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, RiscvCsr, RiscvGpr, RiscvReg};
use crate::util::parse_int::ParseInt;
use crate::util::vmem::Vmem;

use top_earlgrey::top_earlgrey;

/// Command-line parameters.
#[derive(Debug, StructOpt, Clone)]
pub struct SramProgramParams {
    /// Path to the VMEM file to load.
    #[structopt(long, conflicts_with = "elf")]
    pub vmem: Option<PathBuf>,

    /// Path to the ELF file to load.
    #[structopt(long)]
    pub elf: Option<PathBuf>,

    /// Address where to load the VMEM file.
    #[structopt(long, parse(try_from_str = ParseInt::from_str), conflicts_with="elf")]
    pub load_addr: Option<u32>,
}

/// Describe a file to load to SRAM.
#[derive(Debug, Clone)]
pub enum SramProgramFile {
    Vmem { path: PathBuf, load_addr: u32 },
    Elf(PathBuf),
}

impl SramProgramParams {
    // Convert the command line parameters into a nicer structure.
    pub fn get_file(&self) -> SramProgramFile {
        if let Some(path) = &self.vmem {
            SramProgramFile::Vmem {
                path: path.clone(),
                load_addr: self
                    .load_addr
                    .expect("you must provide a load address for a VMEM file"),
            }
        } else {
            SramProgramFile::Elf(
                self.elf
                    .as_ref()
                    .expect("you must provide either an ELF file or a VMEM file")
                    .clone(),
            )
        }
    }

    pub fn load(&self, jtag: &Rc<dyn Jtag>) -> Result<SramProgramInfo> {
        load_sram_program(jtag, &self.get_file())
    }

    pub fn load_and_execute(
        &self,
        jtag: &Rc<dyn Jtag>,
        exec_mode: ExecutionMode,
    ) -> Result<ExecutionResult> {
        load_and_execute_sram_program(jtag, &self.get_file(), exec_mode)
    }
}

/// Execution mode for a SRAM program.
pub enum ExecutionMode {
    /// Jump to the loading address and let the program run forever.
    Jump,
    /// Jump at the loading address and immediately halt execution.
    JumpAndHalt,
    /// Jump at the loading address and wait for the core to halt or timeout.
    JumpAndWait(Duration),
}

/// Detail of execution error of a SRAM program.
#[derive(Debug, Deserialize, Serialize)]
pub enum ExecutionError {
    /// Unknown error.
    Unknown,
    /// The SRAM program loader reported a CRC self-check error.
    CrcMismatch,
}

/// Result of execution of a SRAM program.
#[derive(Debug, Deserialize, Serialize)]
pub enum ExecutionResult {
    /// (JumpAndHalt only) Execution is halted at the beginning.
    HaltedAtStart,
    /// (Jump only) Execution is ongoing.
    Executing,
    /// (JumpAndWait only) Execution successfully stopped.
    ExecutionDone,
    /// (JumpAndWait only) Execution did not finish it time or an error occurred.
    ExecutionError(ExecutionError),
}

/// Errors related to loading an SRAM program.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum LoadSramProgramError {
    #[error("SRAM program execution timed out")]
    Executiontimeout,
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(LoadSramProgramError);

/// Information about the loaded SRAM program
pub struct SramProgramInfo {
    /// Address of the entry point.
    pub entry_point: u32,
    /// CRC32 of the entire data.
    pub crc32: u32,
}

/// Load a program into SRAM using JTAG (VMEM files).
pub fn load_vmem_sram_program(
    jtag: &Rc<dyn Jtag>,
    vmem_filename: &PathBuf,
    load_addr: u32,
) -> Result<SramProgramInfo> {
    log::info!("Loading VMEM file {}", vmem_filename.display());
    let vmem_content = fs::read_to_string(vmem_filename)?;
    let mut vmem = Vmem::from_str(&vmem_content)?;
    vmem.merge_sections();
    log::info!("Uploading program to SRAM at {:x}", load_addr);
    let crc = Crc::<u32>::new(&crc::CRC_32_ISO_HDLC);
    let mut digest = crc.digest();
    for section in vmem.sections() {
        log::info!(
            "Load {} words at address {:x}",
            section.data.len(),
            load_addr + section.addr
        );
        jtag.write_memory32(load_addr + section.addr, &section.data)?;
        // Update CRC
        let mut data8: Vec<u8> = vec![];
        for elem in &section.data {
            data8.write_u32::<LittleEndian>(*elem).unwrap();
        }
        digest.update(&data8);
    }
    Ok(SramProgramInfo {
        entry_point: load_addr,
        crc32: digest.finalize(),
    })
}

/// Load a program into SRAM using JTAG (ELF files).
pub fn load_elf_sram_program(
    jtag: &Rc<dyn Jtag>,
    elf_filename: &PathBuf,
) -> Result<SramProgramInfo> {
    log::info!("Loading ELF file {}", elf_filename.display());
    let file_data = std::fs::read(elf_filename)
        .with_context(|| format!("Could not read ELF file {}.", elf_filename.display()))?;
    let file = object::File::parse(&*file_data)
        .with_context(|| format!("Could not parse ELF file {}", elf_filename.display()))?;
    if file.is_64() {
        bail!("SRAM ELF programs must be 32-bit binaries");
    }
    log::info!("Uploading program to SRAM");
    // The natural thing to do would be to load segments but the GNU linker produces some really
    // unexpected segments for SRAM programs, where the segments can be strictly larger than the
    // data because it aligns everything on a page size (which can changed via a CLI switch but
    // not in the linker file itself). Here is an example:
    //
    // Section Headers:
    //   [Nr] Name              Type            Addr     Off    Size   ES Flg Lk Inf Al
    //   [ 0]                   NULL            00000000 000000 000000 00      0   0  0
    //   [ 1] .text             PROGBITS        10001fc8 000fc8 0064ea 00  AX  0   0  4
    //   [ 2] .rodata           PROGBITS        100084b8 0074b8 0016de 00   A  0   0  8
    //   [ 3] .data             PROGBITS        10009b98 008b98 000084 00  WA  0   0  4
    //   [ 4] .sdata            PROGBITS        10009c1c 008c1c 000000 00   W  0   0  4
    //   [ 5] .bss              NOBITS          10009c1c 008c1c 001f6c 00  WA  0   0  4
    //
    // Program Headers:
    //   Type           Offset   VirtAddr   PhysAddr   FileSiz MemSiz  Flg Align
    //   LOAD           0x000000 0x10001000 0x10001000 0x08c1c 0x0ab88 RWE 0x1000
    //   GNU_STACK      0x000000 0x00000000 0x00000000 0x00000 0x00000 RW  0x10
    //
    // Note that the segment starts at 0x10001000 but .text starts at 0x10001fc8, so loading
    // the segment would actually overwrite the beginning of the SRAM (static critical data).
    // Also note that there is a 6-byte gap between the end of .text and the beginning of .rodata
    // because .rodata needs a bigger alignment.
    //
    // Instead, we elect to load segments that contain loadable data (and not BSS which is cleared
    // by the SRAM CRT). Due to the gap between sections, we have to be careful because the CRT will
    // compute the CRC of the entire data which encompasses all loadable sections but also the gaps
    // between them! The code below explicitly writes the content of the gaps with known values that
    // are taken into account in the CRC value.
    //
    // We also verify (read back and compare) the data from the section that contains the entry point.
    // The rationale is that if the CRC code is corrupted, it could execute the SRAM program even though
    // it should not. By verifying just the tiny bit of code that checks the CRC, we can ensure that the
    // entire program is validated.
    let crc = Crc::<u32>::new(&crc::CRC_32_ISO_HDLC);
    let mut digest = crc.digest();
    let mut last_address: Option<(u32, String)> = None;
    for section in file.sections() {
        let section_name = section.name().unwrap_or("<invalid name>");
        match section.kind() {
            SectionKind::Text
            | SectionKind::Data
            | SectionKind::ReadOnlyData
            | SectionKind::ReadOnlyString => {
                // It is must faster to load data word by word instead of bytes by bytes.
                // The linker script always ensures that we the address and size are multiple of 4.
                const WORD_SIZE: usize = std::mem::size_of::<u32>();
                if section.address() % WORD_SIZE as u64 != 0
                    || section.data()?.len() % WORD_SIZE != 0
                {
                    bail!("The SRAM program must only consists of sections whose address and size are a multiple of the word size");
                }
                // If there is a gap between the last loaded section and this one, fills it and update
                // the CRC.
                if let Some((last_addr, last_sec_name)) = last_address {
                    let gap_size = section.address() as i32 - last_addr as i32;
                    // Just as a sanity check, make sure that the gap is nonnegative and not stupidly large.
                    const MAX_GAP_SIZE: i32 = 128;
                    if gap_size < 0 {
                        bail!(
                            "The SRAM program's sections must be ordered by increasing addresses"
                        );
                    }
                    if gap_size > MAX_GAP_SIZE {
                        bail!("The SRAM program's gap between {} and {} is suspiciously large ({} bytes)",
                            last_sec_name, section_name, gap_size);
                    }
                    let gap_size = gap_size as usize;
                    // This should ways be true because we check alignment above.
                    assert!(
                        gap_size % WORD_SIZE == 0,
                        "the gap size is not a multiple of the word size"
                    );

                    if gap_size > 0 {
                        log::info!(
                            "Fill gap between section {} and {}: {} bytes at address {:x}",
                            last_sec_name,
                            section_name,
                            gap_size,
                            last_addr
                        );
                        let fill_data8: Vec<u8> = std::iter::repeat(0u8).take(gap_size).collect();
                        let fill_data32: Vec<u32> =
                            std::iter::repeat(0u32).take(gap_size / WORD_SIZE).collect();
                        jtag.write_memory32(last_addr, &fill_data32)?;
                        digest.update(&fill_data8);
                    }
                }
                // Write section's data.
                log::info!(
                    "Load section {}: {} bytes at address {:x}",
                    section_name,
                    section.size(),
                    section.address()
                );
                let data32: Vec<u32> = section
                    .data()?
                    .chunks(4)
                    .map(LittleEndian::read_u32)
                    .collect();
                jtag.write_memory32(section.address() as u32, &data32)?;
                digest.update(section.data()?);
                // If this section contains the entry point, read back the data and compare.
                if (section.address()..(section.address() + section.size())).contains(&file.entry())
                {
                    let mut read_data32 = vec![0u32; data32.len()];
                    log::info!("Read back data to verify");
                    jtag.read_memory32(section.address() as u32, &mut read_data32)?;
                    if data32 != read_data32 {
                        bail!("Verification failed: the data loaded in the SRAM was corrupted.");
                    }
                }

                last_address = Some((
                    (section.address() + section.size()) as u32,
                    section_name.to_string(),
                ));
            }
            _ => {
                log::info!(
                    "Skipping section {}",
                    section.name().unwrap_or("<invalid name>")
                );
            }
        }
    }
    Ok(SramProgramInfo {
        entry_point: file.entry() as u32,
        crc32: digest.finalize(),
    })
}

/// Load a program into SRAM using JTAG. Returns the address of the entry point.
pub fn load_sram_program(jtag: &Rc<dyn Jtag>, file: &SramProgramFile) -> Result<SramProgramInfo> {
    match file {
        SramProgramFile::Vmem { path, load_addr } => load_vmem_sram_program(jtag, path, *load_addr),
        SramProgramFile::Elf(path) => load_elf_sram_program(jtag, path),
    }
}

/// Set up the ePMP to enable read/write/execute from SRAM.
/// This function will set the PMP entry 15 to NAPOT to cover the SRAM as RWX
/// This follows the memory layout used by the ROM [0].
///
/// The Ibex core is initialized with a default ePMP configuration [3]
/// when it starts. This configuration has no PMP entry for the RAM
/// and mseccfg.mmwp is set to 1 so accesses that don't match a PMP entry will
/// be denied.
///
/// Before transferring the SRAM program to the device, we must configure
/// the PMP unit to enable reading, writing to and executing from SRAM. Due to
/// implementation details of OpenTitan's hardware debug module, it is important
/// that the RV_ROM remains accessible at all times [1]. It uses entry 13 of the
/// PMP on boot so we want to preserve that. However, we can safely
/// modify the other PMP configuration registers.
///
/// In more detail, the problem is that our debug module implements the
/// "Access Register" abstract command by assembling instructions in the
/// program buffer and then executing the buffer. If one of those
/// instructions clobbers the PMP configuration register that allows
/// execution from the program buffer (PMP entry 13),
/// subsequent instruction fetches will generate exceptions.
///
/// Debug module concepts like abstract commands and the program buffer
/// buffer are defined in "RISC-V External Debug Support Version 0.13.2"
/// [2]. OpenTitan's (vendored-in) implementation lives in
/// hw/vendor/pulp_riscv_dbg.
///
/// [0]: https://opentitan.org/book/sw/device/silicon_creator/rom/doc/memory_protection.html
/// [1]: https://github.com/lowRISC/opentitan/issues/14978
/// [2]: https://riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf
/// [3]: https://github.com/lowRISC/opentitan/blob/master/hw/ip/rv_core_ibex/rtl/ibex_pmp_reset.svh
pub fn prepare_epmp_for_sram(jtag: &Rc<dyn Jtag>) -> Result<()> {
    log::info!("Configure ePMP for SRAM execution");
    let pmpcfg3 = jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::PMPCFG3))?;
    log::info!("Old value of pmpcfg3: {:x}", pmpcfg3);
    // write "L NAPOT X W R" to pmp3cfg in pmpcfg3
    let pmpcfg3 = (pmpcfg3 & 0x00ffffffu32) | 0x9f000000;
    log::info!("New value of pmpcfg3: {:x}", pmpcfg3);
    jtag.write_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::PMPCFG3), pmpcfg3)?;
    // write pmpaddr15 to map the SRAM range
    // hex((0x10000000 >> 2) | ((0x20000 - 1) >> 3)) = 0x4003fff
    let base = top_earlgrey::SRAM_CTRL_MAIN_RAM_BASE_ADDR as u32;
    let size = top_earlgrey::SRAM_CTRL_MAIN_RAM_SIZE_BYTES as u32;
    // make sure that this is a power of two
    assert!(size & (size - 1) == 0);
    let pmpaddr15 = (base >> 2) | ((size - 1) >> 3);
    log::info!("New value of pmpaddr15: {:x}", pmpaddr15);
    jtag.write_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::PMPADDR15), pmpaddr15)?;
    Ok(())
}

/// Execute an already loaded SRAM program. It takes care of setting up the ePMP.
pub fn execute_sram_program(
    jtag: &Rc<dyn Jtag>,
    prog_info: &SramProgramInfo,
    exec_mode: ExecutionMode,
) -> Result<ExecutionResult> {
    prepare_epmp_for_sram(jtag)?;
    // To avoid unexpected behaviors, we always make sure that the return addreess
    // points to an invalid address.
    let ret_addr = 0xdeadbeefu32;
    log::info!("set RA to {:x}", ret_addr);
    jtag.write_riscv_reg(&RiscvReg::GprByName(RiscvGpr::RA), ret_addr)?;
    // The SRAM program loader expects the CRC32 value in a0
    log::info!("set A0 to {:x} (crc32)", prog_info.crc32);
    jtag.write_riscv_reg(&RiscvReg::GprByName(RiscvGpr::A0), prog_info.crc32)?;
    // OpenOCD takes care of invalidating the cache when resuming execution
    match exec_mode {
        ExecutionMode::Jump => {
            log::info!("resume execution at {:x}", prog_info.entry_point);
            jtag.resume_at(prog_info.entry_point)?;
            Ok(ExecutionResult::Executing)
        }
        ExecutionMode::JumpAndHalt => {
            log::info!("set DPC to {:x}", prog_info.entry_point);
            jtag.write_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC), prog_info.entry_point)?;
            Ok(ExecutionResult::HaltedAtStart)
        }
        ExecutionMode::JumpAndWait(tmo) => {
            log::info!("resume execution at {:x}", prog_info.entry_point);
            jtag.resume_at(prog_info.entry_point)?;
            log::info!("wait for execution to stop");
            jtag.wait_halt(tmo)?;
            jtag.halt()?;
            // The SRAM's crt has a protocol to notify us that execution returned: it sets
            // the stack pointer to a certain value.
            let sp = jtag.read_riscv_reg(&RiscvReg::GprByName(RiscvGpr::SP))?;
            match sp {
                SRAM_MAGIC_SP_EXECUTION_DONE => Ok(ExecutionResult::ExecutionDone),
                SRAM_MAGIC_SP_CRC_ERROR => {
                    Ok(ExecutionResult::ExecutionError(ExecutionError::CrcMismatch))
                }
                _ => Ok(ExecutionResult::ExecutionError(ExecutionError::Unknown)),
            }
        }
    }
}

/// Loads and execute a SRAM program. It takes care of setting up the ePMP.
pub fn load_and_execute_sram_program(
    jtag: &Rc<dyn Jtag>,
    file: &SramProgramFile,
    exec_mode: ExecutionMode,
) -> Result<ExecutionResult> {
    let prog_info = load_sram_program(jtag, file)?;
    execute_sram_program(jtag, &prog_info, exec_mode)
}
