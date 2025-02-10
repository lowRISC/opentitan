# Theory of Operation

<%text>## Block Diagram</%text>

![GPIO Block Diagram](../doc/gpio_blockdiagram.svg)

The block diagram above shows the `DATA_OUT` and `DATA_OE` registers
managed by hardware outside of the auto-generated register file.
For reference, it also shows the assumed connections to pads in
the top level netlist.

<%text>## Design Details</%text>

<%text>### GPIO Output logic</%text>

![GPIO Output Diagram](../doc/gpio_output.svg)

The GPIO module maintains one 32-bit output register `DATA_OUT` with two
ways to write to it. Direct write access uses [`DIRECT_OUT`](registers.md#direct_out), and
masked access uses [`MASKED_OUT_UPPER`](registers.md#masked_out_upper) and
[`MASKED_OUT_LOWER`](registers.md#masked_out_lower). Direct access provides full write and read
access for all 32 bits in one register.

For masked access the bits to modify are given as a mask in the upper
16 bits of the [`MASKED_OUT_UPPER`](registers.md#masked_out_upper) and
[`MASKED_OUT_LOWER`](registers.md#masked_out_lower) register write, while the data to write is
provided in the lower 16 bits of the register write.  The hardware updates
`DATA_OUT` with the mask so that the modification is done without software
requiring a Read-Modify-Write.

Reads of masked registers return the lower/upper 16 bits of the `DATA_OUT`
contents. Zeros are returned in the upper 16 bits (mask field). To read
what is on the pins, software should read the [`DATA_IN`](registers.md#data_in) register.
(See [GPIO Input](#gpio-input) section below).

The same concept is duplicated for the output enable register `DATA_OE`.
Direct access uses [`DIRECT_OE`](registers.md#direct_oe), and masked access is available
using [`MASKED_OE_UPPER`](registers.md#masked_oe_upper) and [`MASKED_OE_LOWER`](registers.md#masked_oe_lower).

The output enable is sent to the pad control block to determine if the
pad should drive the `DATA_OUT` value to the associated pin or not.

A typical use pattern is for initialization and suspend/resume code to
use the full access registers to set the output enables and current output
values, then switch to masked access for both `DATA_OUT` and `DATA_OE`.

For GPIO outputs that are not used (either not wired to a pin output or
not selected for pin multiplexing), the output values are disconnected
and have no effect on the GPIO input, regardless of output enable values.

<%text>### GPIO Input</%text>

The [`DATA_IN`](registers.md#data_in) register returns the contents as seen on the
peripheral input, typically from the pads connected to those inputs.  In the
presence of a pin-multiplexing unit, GPIO peripheral inputs that are
not connected to a chip input will be tied to a constant zero input.

The GPIO module provides optional independent noise filter control for
each of the 32 input signals. Each input can be independently enabled with
the [`CTRL_EN_INPUT_FILTER`](registers.md#ctrl_en_input_filter) (one bit per input).  This 16-cycle
filter is applied to both the [`DATA_IN`](registers.md#data_in) register and
the interrupt detection logic. The timing for [`DATA_IN`](registers.md#data_in) is still
not instantaneous if [`CTRL_EN_INPUT_FILTER`](registers.md#ctrl_en_input_filter) is false as there is
top-level routing involved, but no flops are between the chip input and the
[`DATA_IN`](registers.md#data_in) register.

The contents of [`DATA_IN`](registers.md#data_in) are always readable and reflect the
value seen at the chip input pad regardless of the output enable setting from
DATA_OE. If the output enable is true (and the GPIO is connected to a
chip-level pad), the value read from [`DATA_IN`](registers.md#data_in) includes the
effect of the peripheral's driven output (so will only differ from DATA_OUT if
the output driver is unable to switch the pin or during the delay imposed
if the noise filter is enabled).

<%text>#### GPIO Inputs as HW Straps</%text>

The GPIO controller provides an optional feature to sample GPIO input values as hardware configuration straps.
After each reset, on the first cycle when the `strap_en_i` signal is asserted, the GPIO detects its transition from low to high.
One clock cycle later, it samples the GPIO input values and stores them in the `HW_STRAPS_DATA_IN` register.
The `strap_en_i` signal transition from low to high is expected only once after the reset process.
Sampling occurs exclusively at this time, and any subsequent changes to the GPIO input configuration will not be captured.
This mechanism samples all 32 bits of the GPIO input data, regardless of the GPIO output enable status, providing a reliable snapshot of the input values for firmware access.


<%text>### Interrupts</%text>

The GPIO module provides 32 interrupt signals to the main processor.
Each interrupt can be independently enabled, tested, and configured.
Following the standard interrupt guidelines in the [Comportability
Specification](../../../../../doc/contributing/hw/comportability/README.md),
the 32 bits of the [`INTR_ENABLE`](registers.md#intr_enable) register determines whether the
associated inputs are configured to detect interrupt events. If enabled
via the various `INTR_CTRL_EN` registers, their current state can be
read in the [`INTR_STATE`](registers.md#intr_state) register. Clearing is done by writing a
`1` into the associated [`INTR_STATE`](registers.md#intr_state) bit field.

For configuration, there are 4 types of interrupts available per bit,
controlled with four control registers. [`INTR_CTRL_EN_RISING`](registers.md#intr_ctrl_en_rising)
configures the associated input for rising-edge detection.
Similarly, [`INTR_CTRL_EN_FALLING`](registers.md#intr_ctrl_en_falling) detects falling edge inputs.
[`INTR_CTRL_EN_LVLHIGH`](registers.md#intr_ctrl_en_lvlhigh) and [`INTR_CTRL_EN_LVLLOW`](registers.md#intr_ctrl_en_lvllow)
allow the input to be level sensitive interrupts. In theory an input can be
configured to detect both a rising and falling edge, but there is no hardware
assistance to indicate which edge caused the output interrupt.

**Note #1:** The interrupt can only be triggered by GPIO input.
**Note #2:** All inputs are sent through optional noise filtering before being sent into interrupt detection.
**Note #3:** All interrupts to the processor are level interrupts as per the Comportability Specification guidelines.
The GPIO module, if configured, converts an edge detection into a level interrupt to the processor core.
% if num_inp_period_counters > 0:

<%text>### Input Period Counters</%text>

The GPIO module provides ${num_inp_period_counters} (number configurable through a template parameter) input period counters.
Each of those is independent of the others, and each can be independently configured, enabled and disabled, and read out.
A user guide to the counters is provided in the [register documentation](registers.md) and in the [programmer's guide](programmers_guide.md).
The following is a description of the internal mechanics of each of the input period counters.

The selected input is sampled on every positive edge of `clk_i`.

The relevant edge is detected based on the polarity: if the polarity is high, a rising edge is detected if the currently sampled input is low and the new sampled input is high; vice-versa if the polarity is low.

A prescaler counter increments when the input period counter is enabled until the configured prescaler value is reached, then the prescaler counter resets to 0.
For a configured prescaler of 0, the prescaler counter will reach the value in every cycle; for a configured prescaler of 1, the prescaler will reach the value in every second cycle, and so on.
When the prescaler reaches the configured value and the input period counter is enabled, that's an internal event.

A simple FSM controls the actual period counter.
When the input period counter is disabled, the FSM clears to the *disabled* state.
When the input period counter is enabled, the FSM goes into the *pre opening edge* state.
In the *pre opening edge* state, the FSM waits for a relevant edge that starts the period counting (the "opening" edge).
When that edge occurs, the counter starts incrementing and the FSM goes into the *pre closing edge* state.
In the *pre closing edge* state, the counter keeps incrementing on every prescaler event until the next relevant edge.
When the next relevant edge is detected, the counter value is propagated to the SW-visible register and the counter gets cleared to zero.
If continuous mode is not enabled, the `enable` bit in the control register is cleared and the FSM goes back to the *disabled* state.
Otherwise, the FSM stays in the *pre closing edge* state and repeats the actions described for that state.
% endif
