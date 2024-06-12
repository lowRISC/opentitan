// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Context, Result};
use clap::Parser;
use object::{Object, ObjectSymbol};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::cmp::{max, min};
use std::fs;
use std::mem::size_of_val;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{Edge, MonitoringEvent, PinMode};
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::gpio_monitor::{GpioMon, Waves};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(long, value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,

    /// How many random tests to run.
    #[arg(long, default_value = "10")]
    test_count: usize,

    /// Override the random seed used to generate parameters.
    #[arg(long)]
    random_seed: Option<u64>,

    /// Dump waves, even on success (waves are always printed on failured).
    #[arg(long)]
    dump_waves: bool,
}

const PATTGEN_PINS: &[(&str, &str)] = &[
    ("IOR10", "pda0_tx"),
    ("IOR11", "pcl0_tx"),
    ("IOR12", "pda1_tx"),
    ("IOR13", "pcl1_tx"),
];

const CHANNEL_COUNT: usize = 2;
const PATTGEN_MAX_REP: u16 = 5;
// The minimum divisor needs to be sufficiently big so that the transport
// can sample the GPIOs fast enough to get the entire signal.
const PATTGEN_MIN_DIV: u32 = 1000;
const PATTGEN_MAX_DIV: u32 = 15 * PATTGEN_MIN_DIV;
// Maximum allowed clock jitter in ns (this is deviation between observed periods
// and the expected period).
const MAX_CLOCK_JITTER_NS: u64 = 10_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(dead_code)]
enum TestCmd {
    Wait = 0,
    Configure = 1,
    Run = 2,
    Stop = 3,
}

#[derive(Clone)]
struct ChannelSymbols {
    patt_polarity: u32,
    patt_inactive_level_pda: u32,
    patt_inactive_level_pcl: u32,
    patt_div: u32,
    patt_lower: u32,
    patt_upper: u32,
    patt_len: u32,
    patt_rep: u32,
}

struct Symbols {
    test_cmd: u32,
    channel_enable: u32,
    channels: [ChannelSymbols; CHANNEL_COUNT],
}

#[derive(Default, Debug)]
struct PattGenChannelParams {
    patt_polarity: u8,
    patt_inactive_level_pda: u8,
    patt_inactive_level_pcl: u8,
    patt_div: u32,
    patt_lower: u32,
    patt_upper: u32,
    patt_len: u8,
    patt_rep: u16,
}

impl PattGenChannelParams {
    fn from_rng<T: Rng>(rng: &mut T) -> Self {
        PattGenChannelParams {
            patt_polarity: rng.gen_range(0..=1),
            patt_inactive_level_pda: rng.gen_range(0..=1),
            patt_inactive_level_pcl: rng.gen_range(0..=1),
            patt_div: rng.gen_range(PATTGEN_MIN_DIV..=PATTGEN_MAX_DIV),
            patt_lower: rng.gen(),
            patt_upper: rng.gen(),
            patt_len: rng.gen_range(1..=64),
            patt_rep: rng.gen_range(1..=PATTGEN_MAX_REP),
        }
    }

    // Returns the list of clock edges where the data signal changes.
    //
    // When the ENABLE bit is set, the pattgen will start outputting the first
    // bit of the data. Depending on the inactive data value, this may or may
    // not create an edge. At the same time, pattgen will also start outputting
    // the clock signal. Depending on the inactive pcl level and the polarity,
    // this may or may not create an edge. Let us call tFIRST_DATA_EDGE the first time
    // where the data signal has an edge. Corresponding, call tFIRST_CLOCK_EDGE
    // the first time where the clock signal has an edge. We number the clock edges
    // by 0, 1, and so on so that the ith edge is at time tFIRST_CLOCK_EDGE + i*tHALF_PERIOD
    // where tHALF_PERIOD is the half-period of the clock. Then in some combination
    // of inactive pcl/data level, data pattern and clock polarity, it is possible for
    // tFIRST_DATA_EDGE to occur at clock edge "-1", ie tFIRST_DATA_EDGE-tHALF_PERIOD.
    //
    // This function will return the clock edges at which a data edge is expected. They
    // use the number scheme described above. In particular, it is possible for the first
    // data edge to be at index "-1". The edges will include any potential edge needed to
    // return to the inactive value.
    fn pattern_clock_edges(&self) -> Vec<i32> {
        let mut edges = Vec::new();
        let pattern = self.patt_lower as u64 | (self.patt_upper as u64) << 32;
        let mut previous_data = self.patt_inactive_level_pda != 0; // Data line starts at the inactive level.

        // Imagine a baseline scenario where the inactive clock level is 0 and polarity is 0. Then clock edge 0
        // is rising, edge 1 is falling and so on. In this scenario, the ith bit (i=0,1,...) of the pattern
        // appears on the data line between clock edges 2i-1 and 2i+1. The loop below assumes this scenario
        // and pushes a changes at edge 2i-1. To account for other scenarios, the following variable simply adds
        // a constant shift to the 2i-1 above.
        // If polarity is 1 and the inactive clock level is 1 then edge 0 of the clock is falling and edge 1 is
        // rising so the ith pattern bit also appears between edges 2i-1 and 2i+1. Hence the polarity per say does
        // not affect the edge numbering.
        // However, if the inactive clock level does not match the polarity, for example if polarity is 0 but the
        // inactive clock level is 1, then when ENABLE is set, the clock will have a first falling transition that
        // does not correspond to a clock tick and the first "real" clock tick is edge 1.
        // Hence the clock edge numbering is shifted by 1. The same happens if polarity is 1 and inactive pcl level is 0.
        let edge_shift = if (self.patt_polarity != 0) == (self.patt_inactive_level_pcl != 0) {
            -1
        } else {
            0
        };

        for rep in 0..(self.patt_rep as i32) {
            for i in 0..(self.patt_len as i32) {
                let cur_data = (pattern >> i) & 1 == 1;
                if cur_data != previous_data {
                    edges.push(2 * rep * (self.patt_len as i32) + 2 * i + edge_shift);
                    previous_data = cur_data;
                }
            }
        }
        // After the pattern, the hardware will stop with the inactivel value which may create an edge.
        if previous_data != (self.patt_inactive_level_pda != 0) {
            edges.push(2 * (self.patt_rep as i32) * (self.patt_len as i32) + edge_shift)
        }

        edges
    }

    fn clock_period_ns(&self, clk_io_freq_hz: u64) -> u64 {
        // See pattgen documentation.
        1_000_000_000 * (self.patt_div as u64 + 1) / clk_io_freq_hz
    }
}

#[derive(Default, Debug)]
struct PattGenParams {
    channel_enable: u8,
    channels: [PattGenChannelParams; CHANNEL_COUNT],
}

impl PattGenParams {
    fn from_rng<T: Rng>(rng: &mut T) -> Self {
        PattGenParams {
            // Always ensure that at least one channel is enabled.
            channel_enable: rng.gen_range(1..(1 << CHANNEL_COUNT)),
            channels: [(); CHANNEL_COUNT].map(|()| PattGenChannelParams::from_rng(rng)),
        }
    }
}

#[derive(Debug)]
struct SignalWave {
    initial_level: bool,
    // Timestamps in ns.
    edges_ns: Vec<u64>,
}

// Extract the edges from the waves.
fn extract_signal(waves: &Waves, sig_name: &str) -> Result<SignalWave> {
    let clk_idx = waves
        .signal_index(sig_name)
        .with_context(|| format!("no signal {sig_name} monitored?!"))?;
    let initial_level = waves.initial_levels()[clk_idx];
    let mut edges_ns = Vec::new();
    let mut last_value = initial_level;
    for evt in waves
        .all_events()
        .filter(|evt| evt.signal_index == clk_idx as u8)
    {
        ensure!(
            (evt.edge == Edge::Rising && !last_value) || (evt.edge == Edge::Falling && last_value),
            "signal recording is inconsistent, looks like some events were missed"
        );
        last_value = !last_value;
        edges_ns.push(waves.timestamp_to_ns(evt.timestamp));
    }
    Ok(SignalWave {
        initial_level,
        edges_ns,
    })
}

// Verify that a clock signal is valid: it starts with the expected value,
// ticks the required number of times and meetings the expected timing.
fn verify_clock(
    params: &PattGenChannelParams,
    signal: &SignalWave,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // The signal starts with the inactivel clock level.
    ensure!(
        signal.initial_level == (params.patt_inactive_level_pcl == 1),
        "clock starts at the wrong level"
    );
    // The signal must tick exactly the required number of times and go back to the inactive level.
    let expected_ticks = 2 * params.patt_len as usize * params.patt_rep as usize;
    ensure!(
        signal.edges_ns.len() == expected_ticks,
        "clock did not tick the required number of times (expected {}, got {})",
        expected_ticks,
        signal.edges_ns.len()
    );
    // Check that the frequency matches what we expected.
    assert!(signal.edges_ns.len() >= 2);
    let mut min_period_ns = signal.edges_ns[1] - signal.edges_ns[0];
    let mut max_period_ns = min_period_ns;
    for pair in signal.edges_ns.windows(2) {
        min_period_ns = min(min_period_ns, pair[1] - pair[0]);
        max_period_ns = max(max_period_ns, pair[1] - pair[0]);
    }
    let expected_period = params.clock_period_ns(clk_io_freq_hz);
    log::info!(
        "Clock period: expected={expected_period}ns, min={min_period_ns}ns, max={max_period_ns}ns"
    );
    ensure!(
        min_period_ns.abs_diff(expected_period) <= MAX_CLOCK_JITTER_NS,
        "clock has unexpected slow periods"
    );
    ensure!(
        max_period_ns.abs_diff(expected_period) <= MAX_CLOCK_JITTER_NS,
        "clock has unexpected high periods"
    );

    Ok(())
}

// Verify that a data signal is valid.
// This function will add a signal to the waves that contains
// the expected signal.
fn verify_data(
    params: &PattGenChannelParams,
    clk: &SignalWave,
    waves: &mut Waves,
    data_sig_name: &str,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // Then extract the data signal.
    let data = extract_signal(waves, data_sig_name).context("data signal is invalid")?;

    // Compute data edge timing.
    let pattern_edges = params.pattern_clock_edges();

    // Function that returns the time of the nth edge. It needs to handle edge "-1"
    // as well as an another virtual extra edge at the end of the clock signal. See pattern_clock_edges.
    let clk_half_period = params.clock_period_ns(clk_io_freq_hz);
    let clock_nth_edge = |clk_edge_idx: i32| {
        if clk_edge_idx == -1 {
            clk.edges_ns[0] - clk_half_period
        } else if clk_edge_idx == clk.edges_ns.len() as i32 {
            clk.edges_ns.last().unwrap() + clk_half_period
        } else {
            clk.edges_ns[clk_edge_idx as usize]
        }
    };

    // Create a signal in the waves with the expected signal.
    let mut previous_data_val = params.patt_inactive_level_pda != 0;
    let expected_sig_idx = waves.add_signal(format!("{data_sig_name}_expected"), previous_data_val);

    for &clk_edge_idx in &pattern_edges {
        let expected_clk_edge = clock_nth_edge(clk_edge_idx);
        waves.add_event(MonitoringEvent {
            signal_index: expected_sig_idx as u8,
            edge: if previous_data_val {
                Edge::Falling
            } else {
                Edge::Rising
            },
            timestamp: waves.ns_to_timestamp(expected_clk_edge),
        });
        previous_data_val = !previous_data_val;
    }
    waves.sort_events();

    // Data signal must initially be at the inactive data.
    ensure!(
        data.initial_level == (params.patt_inactive_level_pda != 0),
        "data starts at the wrong level"
    );

    for (i, &clk_edge_idx) in pattern_edges.iter().enumerate() {
        let expected_clk_edge = clock_nth_edge(clk_edge_idx);
        let actual_edge = data.edges_ns[i];
        ensure!(
            expected_clk_edge.abs_diff(actual_edge) < MAX_CLOCK_JITTER_NS,
            "data edge {i}: expected a data edge at time {expected_clk_edge}ns (clock edge {clk_edge_idx}) but got time {actual_edge}ns"
        );
    }
    // Check for spurious edges at the end.
    ensure!(
        pattern_edges.len() == data.edges_ns.len(),
        "data has unexpected edges after the pattern, e.g. at time {}",
        data.edges_ns.last().unwrap()
    );

    Ok(())
}

// Verify that the waves match the pattgen parameters.
fn verify_waves(
    params: &PattGenChannelParams,
    waves: &mut Waves,
    clk_sig: &str,
    data_sig: &str,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // First extract the clock signal.
    let clk = extract_signal(waves, clk_sig).context("clock signal is invalid")?;
    // Verify the clock signal.
    verify_clock(params, &clk, clk_io_freq_hz).context("clock signal is invalid")?;
    // Verify the clock signals.
    verify_data(params, &clk, waves, data_sig, clk_io_freq_hz).context("data signal is invalid")?;
    Ok(())
}

fn pattgen_ios(
    opts: &Opts,
    transport: &TransportWrapper,
    uart: &dyn Uart,
    syms: &Symbols,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // Make sure the pins are setup as inputs.
    for (pin, _) in PATTGEN_PINS {
        transport.gpio_pin(pin)?.set_mode(PinMode::Input)?;
    }
    // Create a RNG, either from a given seed or a random one.
    let seed = opts.random_seed.unwrap_or_else(rand::random);
    log::info!("Seed: {seed}");
    let mut rng = StdRng::seed_from_u64(seed);

    for round in 0..opts.test_count {
        let params = PattGenParams::from_rng(&mut rng);
        log::info!("Round {round}:");
        log::info!("{params:#?}");
        // Wait for device to be ready for ujson commands.
        let _ = UartConsole::wait_for(uart, r"SiVal: waiting for commands", opts.timeout)?;
        // Write pattgen parameters.
        write_params(uart, syms, &params)?;
        // Tell device to configure the channels.
        MemWriteReq::execute(uart, syms.test_cmd, &[TestCmd::Configure as u8])?;
        // Wait until done.
        let _ = UartConsole::wait_for(uart, r"Channels configured", opts.timeout)?;
        // Start GPIO monitoring.
        let mut gpio_mon = GpioMon::start(transport, PATTGEN_PINS, true)?;
        // Tell device to start pattern.
        let _ = UartConsole::wait_for(uart, r"SiVal: waiting for commands", opts.timeout)?;
        MemWriteReq::execute(uart, syms.test_cmd, &[TestCmd::Run as u8])?;
        // Wait for device to report the end of this test.
        let _ = UartConsole::wait_for(uart, r"TEST DONE", opts.timeout)?;
        // Stop monitoring.
        let _ = gpio_mon.read(false)?;
        // Get the waves.
        let mut waves: Waves = gpio_mon.try_into()?;
        // Compare the waves.
        for i in 0..CHANNEL_COUNT {
            if (params.channel_enable >> i) & 1 == 1 {
                let res = verify_waves(
                    &params.channels[i],
                    &mut waves,
                    &format!("pcl{i}_tx"),
                    &format!("pda{i}_tx"),
                    clk_io_freq_hz,
                );
                if res.is_err() || opts.dump_waves {
                    log::info!(
                        "====[ VCD dump ]====\n{}\n====[ end dump ]====",
                        waves.dump_vcd()
                    );
                }
                res.with_context(|| format!("channel {i} did not meet expectations"))?;
            }
        }
    }
    // Tell device to stop.
    let _ = UartConsole::wait_for(uart, r"SiVal: waiting for commands", opts.timeout)?;
    MemWriteReq::execute(uart, syms.test_cmd, &[TestCmd::Stop as u8])?;

    // Wait until device has done its work.
    let _ = UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;

    Ok(())
}

fn write_params(uart: &dyn Uart, syms: &Symbols, params: &PattGenParams) -> Result<()> {
    MemWriteReq::execute(
        uart,
        syms.channel_enable,
        &params.channel_enable.to_le_bytes(),
    )?;
    for (chan_syms, chan_param) in std::iter::zip(syms.channels.iter(), params.channels.iter()) {
        MemWriteReq::execute(
            uart,
            chan_syms.patt_polarity,
            &chan_param.patt_polarity.to_le_bytes(),
        )?;
        MemWriteReq::execute(
            uart,
            chan_syms.patt_inactive_level_pcl,
            &chan_param.patt_inactive_level_pcl.to_le_bytes(),
        )?;
        MemWriteReq::execute(
            uart,
            chan_syms.patt_inactive_level_pda,
            &chan_param.patt_inactive_level_pda.to_le_bytes(),
        )?;
        MemWriteReq::execute(uart, chan_syms.patt_div, &chan_param.patt_div.to_le_bytes())?;
        MemWriteReq::execute(
            uart,
            chan_syms.patt_lower,
            &chan_param.patt_lower.to_le_bytes(),
        )?;
        MemWriteReq::execute(
            uart,
            chan_syms.patt_upper,
            &chan_param.patt_upper.to_le_bytes(),
        )?;
        MemWriteReq::execute(uart, chan_syms.patt_len, &chan_param.patt_len.to_le_bytes())?;
        MemWriteReq::execute(uart, chan_syms.patt_rep, &chan_param.patt_rep.to_le_bytes())?;
    }
    Ok(())
}

fn read_symbol<'data: 'file, 'file, T: Object<'data, 'file>>(
    elf: &'file T,
    name: &str,
    size: usize,
) -> Result<u32> {
    let symbol = elf
        .symbols()
        .find(|symbol| symbol.name() == Ok(name))
        .with_context(|| format!("Provided ELF missing '{name}' symbol"))?;
    assert_eq!(
        symbol.size(),
        size as u64,
        "symbol '{name}Real' does not have the expected size"
    );
    Ok(symbol.address() as u32)
}

fn read_backdoor_symbol<'data: 'file, 'file, T: Object<'data, 'file>>(
    elf: &'file T,
    name: &str,
    size: usize,
) -> Result<u32> {
    read_symbol(elf, &format!("{name}Real"), size)
}

fn read_channel_symbol<'data: 'file, 'file, T: Object<'data, 'file>>(
    elf: &'file T,
    name: &str,
    idx: usize,
    size: usize,
) -> Result<u32> {
    read_backdoor_symbol(elf, &format!("{name}{idx}"), size)
}

fn read_channel_symbols<'data: 'file, 'file, T: Object<'data, 'file>>(
    elf: &'file T,
    idx: usize,
) -> Result<ChannelSymbols> {
    let dummy_params = PattGenChannelParams::default();

    Ok(ChannelSymbols {
        patt_polarity: read_channel_symbol(
            elf,
            "kPattPol",
            idx,
            size_of_val(&dummy_params.patt_polarity),
        )?,
        patt_inactive_level_pcl: read_channel_symbol(
            elf,
            "kPattInactiveLevelPcl",
            idx,
            size_of_val(&dummy_params.patt_inactive_level_pcl),
        )?,
        patt_inactive_level_pda: read_channel_symbol(
            elf,
            "kPattInactiveLevelPda",
            idx,
            size_of_val(&dummy_params.patt_inactive_level_pda),
        )?,
        patt_div: read_channel_symbol(elf, "kPattDiv", idx, size_of_val(&dummy_params.patt_div))?,
        patt_lower: read_channel_symbol(
            elf,
            "kPattLower",
            idx,
            size_of_val(&dummy_params.patt_lower),
        )?,
        patt_upper: read_channel_symbol(
            elf,
            "kPattUpper",
            idx,
            size_of_val(&dummy_params.patt_upper),
        )?,
        patt_len: read_channel_symbol(elf, "kPattLen", idx, size_of_val(&dummy_params.patt_len))?,
        patt_rep: read_channel_symbol(elf, "kPattRep", idx, size_of_val(&dummy_params.patt_rep))?,
    })
}

fn read_channels_symbols<'data: 'file, 'file, T: Object<'data, 'file>>(
    elf: &'file T,
) -> Result<[ChannelSymbols; CHANNEL_COUNT]> {
    let chans = (0..CHANNEL_COUNT)
        .map(|i| read_channel_symbols(elf, i))
        .collect::<Result<Vec<ChannelSymbols>>>()?;
    let chans: &[ChannelSymbols; CHANNEL_COUNT] = chans.as_slice().try_into()?;
    Ok(chans.clone())
}

fn read_symbols(opts: &Opts) -> Result<Symbols> {
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;
    let dummy_params = PattGenParams::default();

    Ok(Symbols {
        test_cmd: read_symbol(&elf_file, "test_cmd", 1)?,
        channel_enable: read_backdoor_symbol(
            &elf_file,
            "kChannelEnable",
            size_of_val(&dummy_params.channel_enable),
        )?,
        channels: read_channels_symbols(&elf_file)?,
    })
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let syms = read_symbols(&opts)?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let res = UartConsole::wait_for(&*uart, r"peripheral frequency: ([0-9]+)\r\n", opts.timeout)?;
    let clk_io_freq_hz: u64 = res[1]
        .parse()
        .context("could not parse peripheral frequency")?;
    log::info!("Peripheral clock frequency reported by device: {clk_io_freq_hz} Hz");

    execute_test!(
        pattgen_ios,
        &opts,
        &transport,
        &*uart,
        &syms,
        clk_io_freq_hz
    );
    Ok(())
}
