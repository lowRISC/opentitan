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

    /// Print a VCD dump the expected waves on failure.
    #[arg(long, default_value = "false")]
    print_expected_waves: bool,
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
            patt_div: rng.gen_range(PATTGEN_MIN_DIV..=PATTGEN_MAX_DIV),
            patt_lower: rng.gen(),
            patt_upper: rng.gen(),
            patt_len: rng.gen_range(1..=64),
            patt_rep: rng.gen_range(1..=PATTGEN_MAX_REP),
        }
    }

    // Returns the list of clock edges where the data signal changes.
    // Edge "1" corresponds to the first actual edge of the clock. Since
    // the clock always starts at the right polarity, this means that the
    // first data change can actually happen at edge "0" which does not
    // exist but corresponds to the time of the first edge minus one period.
    // Also return a bool indicate the last value of the pattern.
    fn pattern_clock_edges(&self) -> (Vec<u32>, bool) {
        let mut edges = Vec::new();
        let pattern = self.patt_lower as u64 | (self.patt_upper as u64) << 32;
        let mut previous_data = false; // Data line starts low.
        for rep in 0..(self.patt_rep as u32) {
            for i in 0..(self.patt_len as u32) {
                let cur_data = (pattern >> i) & 1 == 1;
                if cur_data != previous_data {
                    edges.push(2 * rep * (self.patt_len as u32) + 2 * i);
                    previous_data = cur_data;
                }
            }
        }
        // At the end, the hardware will stop with the value of the first bit which could
        // create one more edge.
        let steady_end_val = (self.patt_lower & 1) == 1;
        if steady_end_val != previous_data {
            edges.push(2 * self.patt_rep as u32 * self.patt_len as u32);
        }
        (edges, steady_end_val)
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
fn extract_signal(gpio_mon: &GpioMon, sig_name: &str) -> Result<SignalWave> {
    let clk_idx = gpio_mon
        .signal_index(sig_name)
        .with_context(|| format!("no signal {sig_name} monitored?!"))?;
    let initial_level = gpio_mon.initial_levels()[clk_idx];
    let mut edges_ns = Vec::new();
    let mut last_value = initial_level;
    for evt in gpio_mon.all_events() {
        if evt.signal_index != clk_idx as u8 {
            continue;
        }
        ensure!(
            (evt.edge == Edge::Rising && !last_value) || (evt.edge == Edge::Falling && last_value),
            "signal recording is inconsistent, looks like some events were missed"
        );
        last_value = !last_value;
        edges_ns.push(gpio_mon.timestamp_to_ns(evt.timestamp));
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
    // The signal starts with the polarity.
    ensure!(
        signal.initial_level == (params.patt_polarity == 1),
        "clock starts with the wrong polarity"
    );
    // The signal must tick exactly the required number of times.
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

// Verify that a data signal is valid: TODO
fn verify_data(
    params: &PattGenChannelParams,
    clk: &SignalWave,
    data: &SignalWave,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // Data signal must initially be low.
    ensure!(!data.initial_level, "data starts at the wrong level");
    // Data signal must be low at the end as well.
    ensure!(data.edges_ns.len() % 2 == 0, "data ends at the wrong level");

    // Verify the edge timing.
    let (pattern_edges, last_pattern_value) = params.pattern_clock_edges();
    // The first data edge occur on clock edge "0" which is one period before the first actual edge.
    let virt_pre_edge = clk.edges_ns[0] - params.clock_period_ns(clk_io_freq_hz);
    let mut clock_edges_ns = Vec::new();
    clock_edges_ns.push(virt_pre_edge);
    clock_edges_ns.extend_from_slice(&clk.edges_ns);

    for (i, &clk_edge_idx) in pattern_edges.iter().enumerate() {
        assert!((clk_edge_idx as usize) < clock_edges_ns.len());
        let expected_clk_edge = clock_edges_ns[clk_edge_idx as usize];
        ensure!(i < data.edges_ns.len(),
                "edge {i}: expected a data edge at time {expected_clk_edge}ns (clock edge {clk_edge_idx})");
        let actual_edge = data.edges_ns[i];
        ensure!(
            expected_clk_edge.abs_diff(actual_edge) < MAX_CLOCK_JITTER_NS,
            "edge {i}: expected a data edge at time {expected_clk_edge}ns (clock edge {clk_edge_idx}) but got time {actual_edge}ns"
        );
    }
    // Check for spurious edges at the end: if the last pattern value is one, there will be one extra edge to go down to zero.
    let expected_pattern_edge_count = pattern_edges.len() + if last_pattern_value { 1 } else { 0 };
    ensure!(
        expected_pattern_edge_count == data.edges_ns.len(),
        "data has unexpected edges after the pattern at time {}",
        data.edges_ns.last().unwrap()
    );

    Ok(())
}

// Verify that the waves match the pattgen parameters.
fn verify_waves(
    params: &PattGenChannelParams,
    gpio_mon: &GpioMon,
    clk_sig: &str,
    data_sig: &str,
    clk_io_freq_hz: u64,
) -> Result<()> {
    // First extract the clock signal.
    let clk = extract_signal(gpio_mon, clk_sig).context("clock signal is invalid")?;
    // Verify the clock signal.
    verify_clock(params, &clk, clk_io_freq_hz).context("clock signal is invalid")?;
    // Then extract the data signal.
    let data = extract_signal(gpio_mon, data_sig).context("data signal is invalid")?;
    // Verify the clock signals.
    verify_data(params, &clk, &data, clk_io_freq_hz).context("data signal is invalid")?;
    Ok(())
}

// Print a VCD dump of the expected channel waves.
fn dump_expected_waves(params: &PattGenParams, clk_io_freq_hz: u64) {
    let mut pin_names = Vec::new();
    let mut initial_levels = Vec::new();
    for i in 0..CHANNEL_COUNT {
        pin_names.push(format!("pda{i}_tx"));
        // Data channels always start low.
        initial_levels.push(false);
        pin_names.push(format!("pcl{i}_tx"));
        // Clock channels start at the right polarity if enabled.
        initial_levels
            .push((params.channel_enable >> i) & 1 == 1 && params.channels[i].patt_polarity == 1);
    }

    let mut waves = Waves::new(
        pin_names,
        initial_levels,
        0,
        // Timestamps will be in nanoseconds.
        1_000_000_000,
    );

    // Create events for channels one after the other and sort at the end.
    let mut events = Vec::new();
    for (chan_idx, chan) in params.channels.iter().enumerate() {
        // Add a small offset between initial time and first edge.
        let initial_delay_ns = chan.clock_period_ns(clk_io_freq_hz);
        // Only consider active channels.
        if (params.channel_enable >> chan_idx) & 1 == 0 {
            continue;
        }
        let data_sig_idx = 2 * chan_idx as u8;
        let clk_sig_idx = data_sig_idx + 1;
        let clock_ticks = chan.patt_len as u64 * chan.patt_rep as u64;
        // Add clock.
        for i in 0..clock_ticks {
            events.push(MonitoringEvent {
                signal_index: clk_sig_idx,
                edge: if chan.patt_polarity == 0 {
                    Edge::Rising
                } else {
                    Edge::Falling
                },
                timestamp: initial_delay_ns + (2 * i + 1) * chan.clock_period_ns(clk_io_freq_hz),
            });
            events.push(MonitoringEvent {
                signal_index: clk_sig_idx,
                edge: if chan.patt_polarity == 1 {
                    Edge::Rising
                } else {
                    Edge::Falling
                },
                timestamp: initial_delay_ns + (2 * i + 2) * chan.clock_period_ns(clk_io_freq_hz),
            });
        }
        // Add data.
        let (pattern, steady_end_val) = chan.pattern_clock_edges();
        for (idx, clk_edge) in pattern.iter().enumerate() {
            events.push(MonitoringEvent {
                signal_index: data_sig_idx,
                edge: if (idx % 2) == 0 {
                    Edge::Rising
                } else {
                    Edge::Falling
                },
                timestamp: initial_delay_ns
                    + *clk_edge as u64 * chan.clock_period_ns(clk_io_freq_hz),
            });
        }
        // Add falling edge after pattern with some margin.
        if steady_end_val {
            events.push(MonitoringEvent {
                signal_index: data_sig_idx,
                edge: Edge::Falling,
                timestamp: initial_delay_ns
                    + (2 * clock_ticks + 1) * chan.clock_period_ns(clk_io_freq_hz),
            });
        }
    }
    events.sort_by(|a, b| a.timestamp.cmp(&b.timestamp));
    waves.add_events(&events);

    log::info!(
        "====[ VCD dump of expected waves ]====\n{}\n====[ end dump ]====",
        waves.dump_vcd()
    );
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
        // Compare the waves.
        for i in 0..CHANNEL_COUNT {
            if (params.channel_enable >> i) & 1 == 1 {
                let res = verify_waves(
                    &params.channels[i],
                    &gpio_mon,
                    &format!("pcl{i}_tx"),
                    &format!("pda{i}_tx"),
                    clk_io_freq_hz,
                );
                if res.is_err() && opts.print_expected_waves {
                    log::info!("dump waves");
                    dump_expected_waves(&params, clk_io_freq_hz);
                }
                res.with_context(|| format!("channel {i} did not meet expectations"))?;
            }
        }
        // If we suceeded, do not dump waves.
        gpio_mon.dump_on_drop(false);
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
