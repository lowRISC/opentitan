# Theory of Operation

The ENTROPY_SRC hardware block collects entropy bits from the PTRNG (Physical True Random Number Generator) noise source, performs health tests on the collected entropy bits, packs them, sends them through a conditioning unit, and finally stores them into the `esfinal` FIFO for consumption by firmware or hardware.

It operates in a manner compliant with both FIPS (though NIST SP 800-90B) and CC (AIS31) recommendations.
This revision supports only an external interface for a PTRNG noise source implementation.

### Initialization and Enabling

After power-up, the ENTROPY_SRC block is disabled.
The first step is initialization and enabling.

For simplicity of initialization, only a single write operation to the [`MODULE_ENABLE`](registers.md#module_enable) register is needed to start functional operation of the ENTROPY_SRC block.
This assumes that proper defaults are chosen for the health test thresholds and other registers such as the [`CONF`](registers.md#conf) register.

Once the ENTROPY_SRC block is enabled, also the PTRNG noise source starts up.
The ENTROPY_SRC block will then start to collect entropy bits indefinitely until disabled.

### Boot-Time / Bypass Mode

After a reset, the ENTROPY_SRC block will start up in boot-time / bypass mode by default.
This feature is designed to provide an initial seed's worth of entropy with lower latency than the normal FIPS/CC compliant health check process.
Health testing will still be performed on boot-time mode entropy, but the window of checking is, by default, 384 bits instead of 2048 bits.

### FIPS/CC Compliant Mode

Once the initial boot-time mode phase has completed, the ENTROPY_SRC block can be switched to FIPS/CC compliant mode (for simplicity referred to as FIPS mode) by setting the `FIPS_ENABLE` field in the [`CONF`](registers.md#conf) register to `kMultiBitBool4True`.
In this mode, once the raw entropy has been health checked, it will be passed into a conditioner block.
This block will compress the bits such that the entropy bits/physical bits, or min-entropy value, should be improved over the raw data source min-entropy value.
The compression operation will compress every [`HEALTH_TEST_WINDOWS.FIPS_WINDOW`](registers.md#health_test_windows--fips_window) x 4 tested bits into 384 full-entropy bits.
By default, 2048 tested bits are used.
Note that a seed is only produced if the last [`HEALTH_TEST_WINDOWS.FIPS_WINDOW`](registers.md#health_test_windows--fips_window) x 4 tested bits have passed the health tests.
If a health test fails, the conditioner block continues absorbing the next window unless [`ALERT_SUMMARY_FAIL_COUNTS`](registers.md#alert_summary_fail_counts) reaches the configured [`ALERT_THRESHOLD`](registers.md#alert_threshold).
Once the threshold is reached, the ENTROPY_SRC block stops serving entropy and signals a recoverable alert.
Firmware then needs to disable/re-enable the block to restart operation.

When entropy is delivered to the downstream hardware block, a signal will indicate what type of entropy it is - FIPS/CC compliant or not.
This signal is determined by the `FIPS_FLAG` field in the [`CONF`](registers.md#conf) register.
When `RNG_FIPS` field in the [`CONF`](registers.md#conf) register is set to `kMultiBitBool4True`, the ENTROPY_SRC block will request higher quality entropy from the noise source by asserting the `rng_fips` output signal.

### Startup Health Testing

Note that after enabling the ENTROPY_SRC block, the health tests need to pass for two subsequent windows of [`HEALTH_TEST_WINDOWS.FIPS_WINDOW`](registers.md#health_test_windows--fips_window) x 4 tested bits (startup health testing).
By default, 1024 samples of 4 bits (4096 1-bit samples when running in single-channel mode), i.e., 4096 tested bits, are used for producing the startup seed.
If a health test fails, the startup health testing starts over and the conditioner block continues absorbing the next window.
If the health tests don't pass for two subsequent windows, the ENTROPY_SRC block stops operating and signals a recoverable alert.
Firmware then needs to disable/re-enable the block to restart operation including the startup health testing.

### Firmware Override Mode

The hardware conditioning can also be bypassed and replaced in normal operation with a firmware-defined conditioning algorithm.
This firmware conditioning algorithm can be disabled on boot for security purposes.

The firmware override function has the capability to completely override the hardware health tests and the conditioner paths.
In the case of health tests, firmware can turn off one or all of the health tests and perform the tests in firmware.
A data path is provided in the hardware such that the inbound entropy can be trapped in the observe FIFO.
Once a pre-determined threshold of entropy has been reached in this FIFO, and interrupt is raised to let firmware read the entropy bits out of the FIFO.
The exact mechanism for this functionality starts with setting the [`FW_OV_MODE`](registers.md#fw_ov_control--fw_ov_mode) field in the [`FW_OV_CONTROL`](registers.md#fw_ov_control) register.
This will enable firmware to monitor post-health test entropy bits (including entropy bits used for startup health testing) by reading from the [`FW_OV_RD_DATA`](registers.md#fw_ov_rd_data) register.
Firmware can use the [`OBSERVE_FIFO_THRESH`](registers.md#observe_fifo_thresh) and [`OBSERVE_FIFO_DEPTH`](registers.md#observe_fifo_depth) to determine the state of the OBSERVE FIFO.
At this point, firmware can do additional health checks on the entropy.
Optionally, firmware can do the conditioning function, assuming the hardware is configured to bypass the conditioner block.
Once firmware has processed the entropy, it can then write the results back into the [`FW_OV_WR_DATA`](registers.md#fw_ov_wr_data) register (pre-conditioner FIFO).
The [`FW_OV_ENTROPY_INSERT`](registers.md#fw_ov_control--fw_ov_entropy_insert) in the [`FW_OV_CONTROL`](registers.md#fw_ov_control) register will enable inserting entropy bits back into the entropy flow.
If enabled, any startup health testing has to be performed by the firmware.

An additional feature of the firmware override function is to insert entropy bits into the flow and still use the conditioning function in the hardware.
Setting the [`FW_OV_INSERT_START`](registers.md#fw_ov_sha3_start--fw_ov_insert_start) field in the [`FW_OV_SHA3_START`](registers.md#fw_ov_sha3_start) register will prepare the hardware for this flow.
Once this field is set true, the [`FW_OV_WR_DATA`](registers.md#fw_ov_wr_data) register can be written with entropy bits.
The [`FW_OV_WR_FIFO_FULL`](registers.md#fw_ov_wr_fifo_full) register should be monitored after each write to ensure data is not dropped.
Once all of the data has been written, the [`FW_OV_INSERT_START`](registers.md#fw_ov_sha3_start--fw_ov_insert_start) field should be set to false.
The normal SHA3 processing will continue and finally push the conditioned entropy through the module.

For more details, refer to the [programmer's guide](programmers_guide.md/#firmware-override--bypass-modes).

### Health Tests

Health checks are performed on the input raw data from the PTRNG noise source when in that mode.
There are four health tests that will be performed: repetitive count, adaptive proportion, bucket, and Markov tests.
Each test has a pair of threshold values that determine that pass/fail of the test, one threshold for boot-time / bypass mode, and one for FIPS mode.
By default, all tests are enabled, but can be turned off by setting the thresholds to the maximum value.
Because of the variability of the PTRNG noise source, there are several registers that log statistics associated with the health tests.
For example, the adaptive proportion test has a high watermark register that logs the highest measured number of ones.
The [`ADAPTP_HI_WATERMARKS`](registers.md#adaptp_hi_watermarks) register has an entry for both FIPS and boot-time modes.
This register allows for determining how close the threshold value should be set to the fail over value.
Specific to the adaptive proportion test, there is also the [`ADAPTP_LO_WATERMARKS`](registers.md#adaptp_lo_watermarks) register, which will hold the lowest number of ones measured.
To help understand how well the thresholds work through time, a running count of test fails is kept in the [`ADAPTP_HI_TOTAL_FAILS`](registers.md#adaptp_hi_total_fails) register.
The above example for the adaptive proportion test also applies to the other health tests, with the exception of the low watermark registers.
See the timing diagrams below for more details on how the health tests work.
It should be noted that for all error counter registers, they are sized for 16 bits, which prevents any case where counters might wrap.

Additional, vendor-specific tests are supported through an [external health test interface (xht)](#external-health-tests).

### Health Test Failure Alert

The [`ALERT_THRESHOLD`](registers.md#alert_threshold) register determines during how many subsequent health test windows one or more health test failures can occur before a recoverable alert is raised and the ENTROPY_SRC block stops operating.
In case this threshold is reached, firmware needs to disable/re-enable the block to restart operation including the startup health testing.
By default, the threshold is set to two, such that the occurrence of two failing test cycles back-to-back would provide a very low &alpha; value.
When reaching the threshold while running in [Firmware Override: Extract & Insert mode](programmers_guide.md#firmware_override_-_extract_&_insert), the recoverable alert is not raised nor does the block stop operating.
In other modes, the generation of the recoverable alert can be disabled by configuring a value of zero.

The [`ALERT_SUMMARY_FAIL_COUNTS`](registers.md#alert_summary_fail_counts) register holds the total number of health test windows during which one or more health test failures occurred.
The register is automatically cleared after every passing health test window unless the ENTROPY_SRC is configured in [Firmware Override: Extract & Insert mode](programmers_guide.md#firmware_override_-_extract_&_insert).

The [`ALERT_FAIL_COUNTS`](registers.md#alert_fail_counts) reports the number of health test failures since the last passing health test window on a per-test basis.
If multiple health tests fail for a certain window, the value in [`ALERT_SUMMARY_FAIL_COUNTS`](registers.md#alert_summary_fail_counts) is incremented by just one whereas multiple fields in [`ALERT_FAIL_COUNTS`](registers.md#alert_fail_counts) may get incremented.
The same holds for [`EXTHT_FAIL_COUNTS`](registers.md#extht_fail_counts) which reports the number of external health test failures since the last passing health test window on a per-test basis.

### Routing Entropy to Firmware

Firmware has a path to read entropy from the ENTROPY_SRC block.
The [`ES_ROUTE`](registers.md#entropy_control--es_route) field in the [`ENTROPY_CONTROL`](registers.md#entropy_control) register allows firmware to set the internal multiplexers to steer entropy data to the [`ENTROPY_DATA`](registers.md#entropy_data) register.
When enabled, no entropy is being passed to the block hardware interface.
The control field [`ES_TYPE`](registers.md#entropy_control--es_type) sets whether the entropy will come from the conditioning block or be sourced through the bypass path.
A status bit will be set that can either be polled or generate an interrupt when the entropy bits are available to be read from the [`ENTROPY_DATA`](registers.md#entropy_data) register.
The firmware needs to read the [`ENTROPY_DATA`](registers.md#entropy_data) register twelve times in order to cleanly evacuate the 384-bit seed from the hardware path (12 * 32 bits = 384 bits in total).

### Disabling

At any time, the [`MODULE_ENABLE`](registers.md#module_enable) field can be cleared to halt the entropy generation and health testing.
See the [programmer's guide section](programmers_guide.md/#entropy-source-module-disable) for more details on the ENTROPY_SRC block disable sequence.

## Block Diagram

![ENTROPY_SRC Block Diagram](../doc/entsrc_blk_diag.svg)

## Design Details

### Entropy Dropping and Conditioner Back Pressure

When enabled, the ENTROPY_SRC block has no way to exercise back pressure onto the PTRNG noise source.
Any sample coming in from the noise source is being health tested and continues to flow down the entropy pipeline.
However, if the ENTROPY_SRC block experiences internal back pressure, health tested samples may be dropped in different locations depending on the source of the back pressure and the configured mode of operation.

- **Input of `esfinal` FIFO**: If the `esfinal` FIFO is full, e.g., because the hardware entropy interface doesn't request entropy, entire 384-bit seeds coming out of the conditioner or the bypass packer FIFO get dropped.
  Firmware is not informed when dropping entire seeds.
  When running in [Firmware Override: Extract & Insert mode](programmers_guide.md#firmware_override_-_extract_&_insert), firmware may want to infer whether the next seed is likely going to be dropped at this moment by reading the current depth of the `esfinal` FIFO from the [`DEBUG_STATUS`](registers.md#debug_status) register.
- **Input of Observe FIFO**: When running in any of the [Firmware Override modes](programmers_guide.md#firmware_override_/_bypass_modes) health tested entropy bits are collected in the Observe FIFO for observation / extraction by firmware.
  Whenever the Observe FIFO runs full, the [`FW_OV_RD_FIFO_OVERFLOW`](registers.md#fw_ov_rd_fifo_overflow) bit is asserted and the hardware stops collecting entropy bits in the Observe FIFO until firmware has emptied the FIFO.
  This helps ensuring that observed / extracted entropy bits are contiguous.
- **Input of `postht` / `esbit` FIFO**: When experiencing back pressure from the hardware conditioner (see below), health tested entropy bits may get dropped at the input of the `postht` or `esbit` FIFO when running in multi-channel or single-channel mode, respectively.
  Note that the dropped bits are still health tested and contribute to the overall results for the current window.
  However, to keep the number of bits passed to the conditioner constant, the health test window is stretched by the number of dropped samples.
  Whenever post-health test entropy bits are being dropped from the hardware pipeline, a recoverable alert is triggered and the [`RECOV_ALERT_STS.POSTHT_ENTROPY_DROP_ALERT`](registers.md#recov_alert_sts--postht_entropy_drop_alert) bit is asserted.
  Note that this may also happen in [Firmware Override: Observe mode](programmers_guide.md#firmware_override_-_observe).
  Firmware should thus explicitly check the [`RECOV_ALERT_STS.POSTHT_ENTROPY_DROP_ALERT`](registers.md#recov_alert_sts--postht_entropy_drop_alert) bit to ensure the bits retrieved from the Observe FIFO are indeed contiguous.

The reduce the probability of dropping post-health test entropy bits, the **Distribution FIFO** can be used.
This FIFO has pass-through mode enabled meaning it doesn't add latency to hardware pipeline.
It has a width of 32 bits.
Its depth is configurable via compile-time Verilog parameter and should match the expected level of conditioner back pressure.
The level of conditioner back pressure depends on the following factors:
- The maximum latency for the conditioner to add the padding bits \\(n_{pad}\\) (25 clock cycles) and to run the internal SHA3 primitive \\(n_{sha3}\\) (24 clock cycles).
- The maximum latency of the [CS AES halt request interface](interfaces.md/#inter-module-signals) \\(n_{halt}\\) (48 clock cycles corresponding to CSRNG performing the Update function).

The required depth \\(d_{distr}\\) of the Distribution FIFO can be computed as
$$ d_{distr} = { (r_{ptrng} * s_{symbol}) * (2 * (n_{halt} + n_{sha3}) + n_{pad} + n_{uarch}) - 32 - 64 \over 32} $$

where
- \\(r_{ptrng}\\) is the rate at which the PTRNG noise source generates entropy samples,
- \\(s_{symbol}\\) (= 4) is the symbol size of these samples in bits,
- \\(n_{uarch}\\) (= 5) is the latency of the ENTROPY_SRC micro architecture between producing seeds, and
- the -32 and -64 terms are to account for the number of entropy bits stored in the `postht` and the `precon` FIFOs, respectively.

For [Top Earlgrey](../../../top_earlgrey/README.md), the assumption is that the PTRNG noise source generates entropy bits at a rate of roughly 50 kbps.
With the ENTROPY_SRC block running at 100 MHz, this leads to noise source rate \\(r_{ptrng}\\) = 1/8000.

The noise source model inside the DV environment generates symbols with an average rate of 1 4-bit symbol every 6.5 clock cycles.
To reach functional coverage metrics, the `entropy_src_rng_max_rate` configures the noise source to generate a 4-bit symbol every other clock cycle (\\(r_{ptrng}\\) = 1/2) an the CS AES halt request interface to always respond immediately (\\(n_{halt}\\) = 0).
With these settings, the ENTROPY_SRC block should never drop samples due to conditioner back pressure if a depth of two is chosen for the Distribution FIFO (\\(d_{distr}\\) = 2).


### Security

All module assets and countermeasures performed by hardware are listed in the [countermeasures section](interfaces.md/#security-countermeasures).
Labels for each instance of asset and countermeasure are located throughout the RTL source code.

A configuration and control register locking function is performed by the [`REGWEN`](registers.md#regwen) register.
Clearing the bit in this register will prevent future modification of the [`CONF`](registers.md#conf) register or other writeable registers by firmware.

For all of the health test threshold registers, these registers could be protected with shadow registers.
A design choice was made here to not use shadow registers and save on silicon cost.
The threshold registers are protected by software.
It is expected that software will read the threshold registers on a periodic basis, and compare these values to what was originally programmed into the threshold registers.

Bus integrity checking is performed for the final seed delivery to CSRNG.
This is done to make sure repeated values are not occurring.
Only 64 bits (out of 384 bits) are checked, since this is statistically significant, and more checking would cost more silicon.

### Main State Machine Diagram
The following diagram shows how the main state machine state is constructed.
The larger circles show the how the overall state machine transitions.
The sub-state machines with smaller circles show more detail about how the large circles operate.

![ENTROPY_SRC State Diagram](../doc/es_main_sm.svg)


### Entropy Source Hardware Interface
The following waveform shows an example of how the entropy source hardware interface works, which is much like a FIFO.


```wavejson
{signal: [
   {name: 'clk'           , wave: 'p...|.........|.......'},
   {name: 'es_req'        , wave: '0..1|..01.0..1|.....0.'},
   {name: 'es_ack'        , wave: '0...|.10.10...|....10.'},
   {name: 'es_bus[383:0]' , wave: '0...|.30.30...|....30.', data: ['es0','es1','es2']},
   {name: 'es_fips'       , wave: '0...|....10...|....10.'},
]}
```


### PTRNG Hardware Interface
The following waveform shows an example of what the PTRNG timing looks like.


```wavejson
{signal: [
   {name: 'clk'             , wave: 'p.|......|......|......'},
   {name: 'rng_enable'      , wave: '01|......|......|......'},
   {name: 'rng_valid'       , wave: '0.|..10..|..10..|..10..'},
   {name: 'rng_b'           , wave: 'x.|..3...|..4...|..5.....', data: ['es0','es1','es2']},
]}
```

### Repetition Count Test
The following waveform shows how a sampling of a data pattern will be tested by the Repetition Count test.
Operating on each bit stream, this test will count when a signal is at a stuck level.
This NIST test is intended to signal a catastrophic failure with the PTRNG noise source.

Note that as per definition in SP 800-90B, the Repetition Count test does not operate on a fixed window.
The repetition count test fails if any sequence of bits continuously asserts the same value for too many samples, as determined by the programmable threshold, regardless of whether that sequence crosses any window boundaries.


```wavejson
{signal: [
   {name: 'rng_valid'      , wave: 'p...............'},
  ['rng bits',
   {name: 'rng_bus[3]'     , wave: '1.0.10..1...0101'},
   {name: 'rng_bus[2]'     , wave: '01.0.10..1...010'},
   {name: 'rng_bus[1]'     , wave: '101.0.10..1...01'},
   {name: 'rng_bus[0]'     , wave: '10.10..1...0101.'},
   ],
   {name: 'thresh_i (hex)'      , wave: '3...............',data: ['3']},
   {name: 'rep_cntr_q[3] (hex)' , wave: '4444444444444444',data: ['0','0','1','0','1','0','0','1','2','0','1','2','3','0','0','0']},
   {name: 'rep_cntr_q[2] (hex)' , wave: '4444444444444444',data: ['0','1','0','1','0','1','0','0','1','2','0','1','2','3','0','0']},
   {name: 'rep_cntr_q[1] (hex)' , wave: '4444444444444444',data: ['0','0','0','0','1','0','1','0','0','1','2','0','1','2','3','0']},
   {name: 'rep_cntr_q[0] (hex)' , wave: '4444444444444444',data: ['0','0','0','1','0','0','1','2','0','1','2','3','0','0','0','0']},
   {name: 'test_cnt_q (hex)'    , wave: '4444444444444444',data: ['0','0','0','0','0','0','0','0','0','0','0','1','2','3','4','0']},
   {name: 'window_cnt_q (hex)'  , wave: '5555555555555555',data: ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']},
], head:{
   text:'Repetition Count Test',
   tick:0,
  },}
```

### Adaptive Proportion Test
This NIST-defined test is intended to detect statistical bias in the raw entropy data.
The test counts the number of 1's in a given sample, and applies thresholds to reject samples which deviate too far from the ideal mean of 50%.

Depending on the value of the [`CONF.THRESHOLD_SCOPE`](registers.md#conf) field, the thresholds can either be applied collectively to the all RNG inputs, or the thresholds can be applied on a line-by-line basis.
Setting [`CONF.THRESHOLD_SCOPE`](registers.md#conf) to `kMultiBitBool4True` will apply the thresholds to the aggregated RNG stream.
This can be useful for lowering the likelihood of coincidental test failures (higher &alpha;).
Meanwhile, setting [`CONF.THRESHOLD_SCOPE`](registers.md#conf) to `kMultiBitBool4False` will apply thresholds on a line-by-line basis which allows the ENTROPY_SRC to detect single line failures.

The following waveform shows how a sampling of a data pattern will be tested by the Adaptive Proportion test.
In this example, the sum is taken over all RNG lines (i.e., [`CONF.THRESHOLD_SCOPE`](registers.md#conf) is True).

```wavejson
{signal: [
   {name: 'rng_valid'      , wave: 'p...............'},
  ['rng bits',
   {name: 'rng_bus[3]'     , wave: '1.0.10..1...0101'},
   {name: 'rng_bus[2]'     , wave: '01.0.10..1...010'},
   {name: 'rng_bus[1]'     , wave: '101.0.10..1...01'},
   {name: 'rng_bus[0]'     , wave: '10.10..1...0101.'},
   ],
   {name: 'Column-wise sum'   , wave: '3333333333333333',data: ['3','2','2','2','1','1','1','1','2','3', '4', '3', '3', '2', '2','3']},
   {name: 'test_cnt_q (hex)'   , wave: '4444444444444444',data: ['0','3','5','7','9','a','b','c','d','f','12','16','19','1c','1e','20']},
   {name: 'window_cnt_q (hex)' , wave: '5555555555555555',data: ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']},
], head:{
   text:'Adaptive Proportion Test',
   tick:0,
  },}
```

### Bucket Test
The following waveform shows how a sampling of a data pattern will be tested by the Bucket test.
Operating on all four bit streams, this test will identify the symbol and sort it into bin counters, or "buckets".
This test is intended to find bias with a symbol or symbols.

```wavejson
{signal: [
   {name: 'rng_valid'      , wave: 'p...............'},
  ['rng bits',
   {name: 'rng_bus[3]'     , wave: '1.0.10..1...0101'},
   {name: 'rng_bus[2]'     , wave: '01.0.10..1...010'},
   {name: 'rng_bus[1]'     , wave: '101.0.10..1...01'},
   {name: 'rng_bus[0]'     , wave: '10.10..1...0101.'},
   ],
   {name: 'thresh_i (hex)'       , wave: '3...............',data: ['3']},
   {name: 'bin_cntr_q[0] (hex)'  , wave: '4...............',data: ['0']},
   {name: 'bin_cntr_q[1] (hex)'  , wave: '4........4......',data: ['0','1']},
   {name: 'bin_cntr_q[2] (hex)'  , wave: '4.......4.......',data: ['0','1']},
   {name: 'bin_cntr_q[13] (hex)' , wave: '4..........4....',data: ['0','1']},
   {name: 'bin_cntr_q[14] (hex)' , wave: '4............4..',data: ['0','1']},
   {name: 'bin_cntr_q[15] (hex)' , wave: '4...........4...',data: ['0','1']},
   {name: 'test_cnt_q (hex)'     , wave: '4...............',data: ['0']},
   {name: 'window_cnt_q (hex)' , wave: '5555555555555555',data: ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']},
], head:{
   text:'Bucket Test',
   tick:0,
  },}
```

### Markov Test
The following waveform shows how a sampling of a data pattern will be tested by the Markov test.

The test aims to detect either:

1. Oversampling of AST/RNG outputs leading to "clustered" input values that eventually change, but often are just repeats of the previous sample.
For example the string: "00111111000011000111000111000001111" has roughly equal numbers of 1's and 0's, but no good entropy source should generate such strings, because each bit is likely just a repeat of the previous one.

2. Wild oscillations of the RNG, in a distinctly non-random way.
For instance the string: "010101010101010101" has almost zero entropy, even though the number of 1's and 0's appears unbiased.

The test counts the number of changes in the a fixed number of RNG samples, and comparing the number of "01"/"10" pairs to the number of "00"/"11" pairs.
On average, the number of switching (e.g., "01") vs. non-switching (e.g., "00") pairs should be 50% of the total, with a variance proportional to the sample size.

Like the Adaptive Proportion test, the Markov Test can be computed either cumulatively (summing the results over all RNG lines) or on a per-line basis.
In this example, the RNG lines are scored individually (i.e., [`CONF.THRESHOLD_SCOPE`](registers.md#conf) is False).

```wavejson
{signal: [
   {name: 'rng_valid'      , wave: 'p...............'},
  ['rng bits',
   {name: 'rng_bus[3]'     , wave: '1.0.10..1...0101'},
   {name: 'rng_bus[2]'     , wave: '01.0.10..1...010'},
   {name: 'rng_bus[1]'     , wave: '101.0.10..1...01'},
   {name: 'rng_bus[0]'     , wave: '10.10..1...0101.'},
   ],
   {name: 'pair_cntr_q[3] (hex)', wave: '4.4.4.4.4.4.4.4.',data: ['0','0','0','1','1','1','1','2']},
   {name: 'pair_cntr_q[2] (hex)', wave: '4.4.4.4.4.4.4.4.',data: ['0','1','2','3','3','4','4','5']},
   {name: 'pair_cntr_q[1] (hex)', wave: '4.4.4.4.4.4.4.4.',data: ['0','1','1','1','2','2','2','2']},
   {name: 'pair_cntr_q[0] (hex)', wave: '4.4.4.4.4.4.4.4.',data: ['0','1','2','2','3','3','4','5']},
   {name: 'window_cnt_q (hex)'  , wave: '5555555555555555',data: ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']},
], head:{
   text:'Markov Test',
   tick:0,
  },}
```

### External Health Tests

Vendor-specific tests are supported through an external health test interface (xht).
This is the same interface that is used for the internal health tests.
Below is a description of this interface:
- entropy_bit: 4-bit wide bus of entropy to be tested.
- entropy_bit_valid: indication of when the entropy is valid.
- rng_bit_en: indication whether running in single-channel or multi-channel mode.
- rng_bit_sel: 2-bit signal to indicate the selected channel when running in single-channel mode.
- clear: signal to clear counters, and is register driven.
- active: signal to indicate when the test should run, and is register driven.
- thresh_hi: field to indicate what high threshold the test should use, and is register driven.
- thresh_lo: field to indicate what low threshold the test should use, and is register driven.
- health_test_window: 18-bit signal indicating the length of the health test window in symbols.
- window_wrap_pulse: field to indicate the end of the current window.
- threshold_scope: field to indicate whether the thresholds are intended to be applied to all entropy lines collectively or on a line-by-line basis, to be read from a register.
- test_cnt_hi: 16-bit generic test count high result, to be read from a register.
- test_cnt_low: 16-bit generic test count low result, to be read from a register.
- continuous_test: signal to indicate whether the test is running continuously across health test window boundaries.
- test_fail_hi_pulse: indication that a high threshold comparison failed, to be read from a register.
- test_fail_lo_pulse: indication that a low threshold comparison failed, to be read from a register.
