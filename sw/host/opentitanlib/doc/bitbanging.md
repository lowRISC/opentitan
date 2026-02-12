# Bitbanging Utilities

OpenTitanLib provides several test utilities that can be used alongside GPIO bitbanging and monitoring transport interfaces to bitbang common protocols.

These can be useful for testing different OpenTitan peripherals, by bitbanging invalid transactions or other edge cases that cannot be supported by regular transport devices.
This allows for more thorough software testing to check that OpenTitan hardware can handle and respond to these cases correctly.

Bitbanging can also be useful for custom workflows that only support bitbanging, or which require the generation of VCD files corresponding to different host/device transactions.
One example of such a workflow might be the manufacturing process, which may require VCD files as inputs. See [*VCD Integration*](#vcd-integration) for more detail.

## Supported Utilities

Currently, bitbanging utilities are available for:
* [UART](../src/test_utils/bitbanging/uart.rs)
* [SPI](../src/test_utils/bitbanging/spi.rs)
* [I2C](../src/test_utils/bitbanging/i2c.rs)
* [PWM](../src/test_utils/bitbanging/pwm.rs)

Each of these utilities are designed to be self-contained libraries, producing and consuming waveforms represented by uniform discrete samples, where each bit in each sample describes the state (0 or 1) of a pin at a given time.
These are intended to be used with the OpenTitanLib `GpioBitbanging` interface directly.

For asynchronous transmissions such as UART RX, this means that received edge events from the `GpioMonitoring` interface must first be sampled before being input into the UART decoding interface (see [*UART Receive*](#uart-receive)).

## SPI Bitbanging

The [SPI bitbanging tools](../src/test_utils/bitbanging/spi.rs) provide a `SpiBitbangEncoder`, which can be used to encode SPI writes and reads as a SPI host, and a `SpiBitbangDecoder`, which can be used to decode SPI reads from the perspective of either a SPI Host or a SPI device.

These can each be configured via the `SpiBitbangConfig` provided during their creation, with options to configure the clock polarity (CPOL), clock phase (CPHA), data mode (Single, Dual or Quad) and the number of bits per SPI word.
Dual Data Rate (DDR) is not currently supported.

Additionally, delays can optionally be added to support communication with a wider range of SPI devices.
This includes delays between CS assertion/de-assertion and the SPI words, as well as additional delays between each SPI word.
The decoding functionality uses the varying clock and chip-select edges to decode the transaction, meaning that the decoder does not need to be provided with these delays.

To bitbang SPI, samples from the SPI clock (CLK/SCK), chip select (CS) and data lines (D0/D1/D2/D3) are required.
When using single or dual data mode, only the values of D0 (COPI) and D1 (CIPO) are used.

You must also appropriately configure the corresponding GPIO pins before bitbanging:
 * `CLK` must be PushPull, and its current idle level should match your CPOL configuration.
 * `CS` must be PushPull, and should be idle high.
 * The data lines are configured according to the data mode being used.
 Standard single data mode SPI uses COPI/D0 in PushPull and CIPO/D1 in Input.

To use the bitbanging tools with the `GpioBitbanging` interface, you must wrap the encoded samples in a `BitbangEntry`.
For transactions involving only writes, it suffices to use a `BitbangEntry::Write(&samples)`, but if any read is involved then `BitbangEntry::Both(&samples, &mut read_samples)` must be used.
Simultaneous bidirectional SPI transmissions can be achieved by simply encoding a regular SPI write, and using `BitbangEntry::Both` to get the read contents. A period equivalent to half the period of the desired clock rate should be used for bitbanging, as there are 2 samples per clock (for the falling and rising edges).

One final quirk to note is that the bitbanging interface captures inputs before applying outputs, meaning that one extra sample must be appended to capture the final read input for decoding.

An example illustrating how to integrate these tools is shown below:

```rs
/* Setup pins, buffers, clock rate etc... */

// Encode a SPI transmission
let config = SpiBitbangConfig {
    cpol: false,
    cpha: false,
    data_mode: SpiDataMode::Single,
    bits_per_word: 8,
};
let delays = SpiEncodingDelays {
    inter_word_delay: 0,
    cs_hold_delay: 1,
    cs_release_delay: 1,
};
let mut encoder = SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(config.clone(), delays);
let mut samples = Vec::new();
encoder.assert_cs(true, &mut samples);
encoder.encode_write(&wbuf, &mut samples)?; /* also use for bidirectional SPI */
encoder.encode_read(rbuf.len(), &mut samples)?;
encoder.assert_cs(false, &mut samples);

// Add an extra sample to ensure we read the last input
samples.push(*samples.last().unwrap());

// Send the encoded transmission over the GpioBitbanging interface.
// Make sure the order of `gpio_pins` matches the encoding generics.
let mut read_samples = vec![0; samples.len()];
let waveform = Box::new([BitbangEntry::Both(&samples, &mut read_samples)]);
let period = Duration::from_nanos((1_000_000_000u64 / clock_rate as u64) / 2);
transport
    .gpio_bitbanging()?
    .run(&gpio_pins, period, waveform)?;

// Decoding the SPI reads (from the host's perspective)
let decoder = SpiBitbangDecoder::<2, 3, 4, 5, 0, 1>::new(config, SpiEndpoint::Host);
let decoded = decoder.run(read_samples[1..].to_vec())?;
rbuf.copy_from_slice(&decoded);
```

Further examples can be seen in the unit tests in [`spi.rs`](../src/test_utils/bitbanging/spi.rs).

## UART Bitbanging

The [UART bitbanging tools](../src/test_utils/bitbanging/uart.rs) provide a `UartBitbangEncoder` and a `UartBitbangDecoder` for transmitting and receiving respectively.

These can each be configured via the `UartBitbangConfig` provided during their creation, with options to configure the number of data & stop bits, parity, and a standard length for break conditions.
Use of more than 8 data bits or 1.5 stop bits is currently unsupported.

Bitbanging UART transmissions only requires samples from the TX or RX for pin for encoding and decoding respectively.
These samples are assumed to be stored in the least significant bit of the provided samples.
The `TX` pin should be configured in PushPull mode with idle high, whereas the `RX` pin should be configured in Input mode.

### UART Transmit

To use the encoder with the `GpioBitbanging` interface, you must wrap the encoded samples in a `BitbangEntry::Write(&samples)`, and provide a period that is calculated from the configured baud rate.
Because UART is an asynchronous protocol and its synchronization is based on timing, you should be careful about the maximum bitbanging frequency that your backend supports.
For example, the HyperDebug backend can accurately support 57600 Bd, but skews too much at the standard 115200 Bd, causing sent UART data to be infrequently corrupted.


The following example shows how you might bitbang a UART transmission:

```rs
/* Setup TX pin, write buffer and baud rate... */

// Encode a UART transmission
let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
let encoder = UartBitbangEncoder::new(config);
let mut samples = vec![];
encoder.encode_characters(&wbuf, &mut samples);

// Send the encoded transmission over the GpioBitbanging interface
let waveform = Box::new([BitbangEntry::Write(&samples)]);
let period = Duration::from_nanos(1_000_000_000u64 / baud_rate as u64);
transport
    .gpio_bitbanging()?
    .run(&[tx_pin.borrow()], period, waveform)?;
```

To encode the transmission of a break condition, you can either use the encoding interface:

```rs
let mut samples = vec![];
encoder.encode_break(&mut samples);
/* Send the encoded transmission over the GpioBitbanging interface... */
```

or you can manually configure the GPIO pin directly to hold the TX pin low for the desired duration.

### UART Receive

Receiving a bitbanged UART transmission is more difficult due to the asynchronous nature of UART.
You can use OpenTitanLib's `GpioMonitoring` interface to start monitoring incoming GPIO edge events on the RX pin in the background:

```rs
let gpio_monitoring = transport.gpio_monitoring()?;
let start = gpio_monitoring.monitoring_start(&[rx_pin.borrow()])?;
```

And then at any point you can poll and read previously monitored events from the interface:

```rs
// Use `true` to continue monitoring afterwards, or `false` to stop here.
let read_response = gpio_monitoring.monitoring_read(&[rx_pin.borrow()], true)?;
```

You can then use the additional [`UartRxMonitoringDecoder`](../src/test_utils/bitbanging/uart_rx_sampling.rs) wrapper which will consume these responses and perform the required sampling and decoding.
When using this interface, you must pass *all* monitoring read responses to the decoder, as missing edges could cause errors.
Note also that if you start monitoring mid-transmission, incoming UART data will be dropped until the RX line stays idle or in a break condition for at least a length of time corresponding to 1 UART frame.

For example, you might use it as follows:

```rs
/* Setup rx pin, baud_rate, etc... */

// Start monitoring the RX pin and set up the decoder
let gpio_monitoring = transport.gpio_monitoring()?;
let start = gpio_monitoring.monitoring_start(&[rx_pin.borrow()])?;
let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
let decoder = UartBitbangDecoder::new(config);
let clock_nature = gpio_monitoring.get_clock_nature()?;
let mut monitor_decoder = UartRxMonitoringDecoder::new(decoder, clock_nature, start)?;

// After some time has passed, read the monitoring response and decode
let read_response = gpio_monitoring.monitoring_read(&[rx_pin.borrow()], true)?;
let signal_index = 0u8; /* RX pin is signal 0 in our monitoring read */
let decoded = monitor_decoder.decode_response(read_response, signal_index, baud_rate)?;
```

Further examples can be seen in the unit tests in [`uart.rs`](../src/test_utils/bitbanging/uart.rs) and [`uart_rx_sampling.rs`](../src/test_utils/bitbanging/uart_rx_sampling.rs).

## VCD Integration

For some flows (e.g. manufacturing), it may be useful to be able to output bitbanged transactions as VCDs, which can be used with e.g. provisioning equipment.
This section provides further guidance on integrating these utilities.

OpenTitanLib has some [VCD tools](../src/util/vcd.rs) which can be used for dumping and parsing VCD files from/to the different GPIO bitbanging formats supported by OpenTitanLib.
These tools operate using `Vcd` structs, which can be loaded & dumped directly from/to a string using the `load_vcd` and `dump_vcd` functions.
Alternatively, by using the `VcdParser` and `VcdWriter` implementations directly, you can write to or read from a file (or any other writable/readable context).

The `vcd_from_samples` function can be used to translate the uniform samples returned by the `GpioBitbanging` interface to a `Vcd`, and the `UniformVcdSampler` does the inverse - providing an iterator over a given `Vcd` to retrieve uniform samples.
Note that currently, signals are dumped into the generated VCD in the order that pins are provided, and loaded in the same order (the order listed in the VarDefs section of the VCD).
The VCD sampling functionality is designed to be able to work with waveforms containing an arbitrary number of signals, so instead of directly providing `u8` samples, you should convert each sample to a slice first.

Shown below is some examples of how you might use this, integrated with the bitbanging utilities:

```rs
// ... Finish encoding a bitbanged SPI transmission
encoder.assert_cs(false, &mut samples);
samples.push(*samples.last().unwrap());

// Record it as a VCD to store and replay later
let pin_names = vec![
    Some("spi_sck".into()),
    Some("spi_cs".into()),
    Some("spi_copi".into()),
];
let period = Duration::from_nanos((1_000_000_000u64 / clock_rate as u64) / 2);
let sample_slices = samples.iter().map(std::slice::from_ref).collect::<Vec<_>>();
let vcd = vcd_from_samples(pin_names, period.as_nanos() * 1000, &sample_slices)?;
let vcd_str = dump_vcd(&vcd)?;
log::info!("{}", vcd_str);

// Load a VCD from a string
let vcd = load_vcd(&vcd_str)?;

// Retrieve pin & timescale info (which we can use as the bitbanging period)
log::info!("Pin names: {:?}", vcd.var_names());
let decoded_timescale_ps = vcd.header.timescale_ps.unwrap();
let period = Duration::from_nanos((decoded_timescale_ps / 1000) as u64);

// Dump the VCD to some bitbanging samples
let decoded = UniformVcdSampler::new(vcd, 1).collect::<Result<Vec<_>>>()?;
let decoded_samples = decoded.iter().map(|s| s[0]).collect::<Vec<_>>();

// Play the bitbanged samples from the VCD
let waveform = Box::new([BitbangEntry::Write(&decoded_samples)]);
transport
    .gpio_bitbanging()?
    .run(&gpio_pins, period, waveform)?;
```

Similarly, the `vcd_from_edges` function translates the `GpioMonitoring` edge responses to a `Vcd`, an the `vcd_to_edges` performs the inverse operation, creating an equivalent `MonitoringReadResponse`.
This can be used for example with the UART RX samples:

```rs
// Read the RX pin samples from `GpioMonitoring`
let gpio_monitoring = transport.gpio_monitoring()?;
let start = gpio_monitoring.monitoring_start(&[rx_pin.borrow()])?;
/* ... */
let read_response = gpio_monitoring.monitoring_read(&[rx_pin.borrow()], true)?;

// Record it as a VCD to store and decode later
let clock_nature = gpio_monitoring.get_clock_nature()?;
let ClockNature::Wallclock { resolution, .. } = clock_nature else {
    bail!("Could not get clock resolution");
};
let pin_names = vec![Some("uart_rx".into())];
let vcd = vcd_from_edges(
    pin_names,
    resolution,
    start.timestamp,
    &start.initial_levels,
    &read_response.events,
    read_response.timestamp,
)?;
let vcd_str = dump_vcd(&vcd)?;
log::info!("{}", vcd_str);

// Load a VCD from a string
let vcd = load_vcd(&vcd_str)?;

// To reproduce the exact response, you must provide the same start timestamp,
// but this only changes the offset of the incoming edges. This should match
// the timestamp of the start response used by the `UartRxMonitoringDecoder`.
let decoded = vcd_to_edges(vcd, resolution, start.timestamp)?;
log::info!("Pin variables: {:?}", decoded.pin_vars);

// Decode the bitbanged samples from the VCD
let signal_index = 0u8;
let decoded = monitor_decoder.decode_response(read_response, signal_index, baud_rate)?;
```

Further examples can be seen in the unit tests in [`vcd.rs`](../src/util/vcd.rs).
