# Theory of Operation

## Block Diagram

![AON Timer Block Diagram](../doc/aon_timer_block_diagram.svg)

See the block diagram for high level function and connectivity.
The timer interacts with the CPU core and the power manager and reset manager to drive wakeup / reset events and interrupts.
There is also an extra input to tell the counter whether to run ("counter-run").
This is used to stop the watchdog timer running when in debugging mode or when the alert handler has put the system in a "killed" state.

## Design Details

The always-on timer will run on a ~200KHz clock.
The timers themselves are 32b wide, giving a maximum timeout window of roughly ~6 hours.
For the wakeup timer, the pre-scaler extends the maximum timeout to ~1000 days.

Register reads via the TLUL interface are synchronized to the slow clock using the "async" register generation feature.
This means that writes can complete before the data has reached its underlying register in the slow clock domain.
If software needs to guarantee completion of a register write, it can read back the register value (which will guarantee the completion of all previous writes to the peripheral).
