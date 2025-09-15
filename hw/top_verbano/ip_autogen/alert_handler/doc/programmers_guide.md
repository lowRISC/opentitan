# Programmer's Guide


## Power-up and Reset Considerations

False alerts during power-up and reset are not possible since the alerts are disabled by default, and need to be configured and locked in by the firmware.
The ping timer won't start until initial configuration is over and the registers are locked in.

The low-power state management of alert channels is handled entirely by hardware and hence this is transparent to software.
Note however that the LPGs inherit the security properties of the associated clock groups and resets.
This means that the low-power state of certain alerts can be controlled by SW by means of clock gating or block reset.
For example, certain crypto blocks are located in a transactional clock group which can be clock gated by SW - and this also affects the associated alerts of these crypto blocks.
See [clock](../../clkmgr/README.md) and [reset managers](../../rstmgr/README.md) for more detail.


## Initialization

To initialize the block, software running at a high privilege levels (early in the security settings process) should do the following:

1. For each alert and each local alert:

    - Determine if alert is enabled (should only be false if alert is known to be faulty).
      Set [`ALERT_EN_SHADOWED_0.EN_A_0`](../data/alert_handler.hjson#alert_en_shadowed_0) and [`LOC_ALERT_EN_SHADOWED_0.EN_LA_0`](../data/alert_handler.hjson#loc_alert_en_shadowed_0) accordingly.

    - Determine which class (A..D) the alert is associated with.
      Set [`ALERT_CLASS_SHADOWED_0.CLASS_A_0`](../data/alert_handler.hjson#alert_class_shadowed_0) and [`LOC_ALERT_CLASS_SHADOWED_0.CLASS_LA_0`](../data/alert_handler.hjson#loc_alert_class_shadowed_0) accordingly.

    - Optionally lock each alert configuration by writing 0 to [`ALERT_REGWEN_0.EN_0`](../data/alert_handler.hjson#alert_regwen_0) or [`LOC_ALERT_REGWEN_0.EN_0`](../data/alert_handler.hjson#loc_alert_regwen_0).
      Note however that only **locked and enabled** alerts are going to be pinged using the ping mechanism.
      This ensures that spurious ping failures cannot occur when previously enabled alerts are being disabled again (before locking).


2. Set the ping timeout value [`PING_TIMEOUT_CYC_SHADOWED`](../data/alert_handler.hjson#ping_timeout_cyc_shadowed).
   This value is dependent on the clock ratios present in the system.

3. For each class (A..D):

    - Determine whether to enable escalation mechanisms (accumulation / interrupt timeout) for this particular class. Set [`CLASSA_CTRL_SHADOWED.EN`](../data/alert_handler.hjson#classa_ctrl_shadowed) accordingly.

    - Determine if this class of alerts allows clearing of escalation once it has begun.
      Set [`CLASSA_CTRL_SHADOWED.LOCK`](../data/alert_handler.hjson#classa_ctrl_shadowed) to true if clearing should be disabled.
      If true, once escalation protocol begins, it can not be stopped, the assumption being that it ends in a chip reset else it will be rendered useless thenceforth.

    - Determine the number of alerts required to be accumulated before escalation protocol kicks in. Set [`CLASSA_ACCUM_THRESH`](../data/alert_handler.hjson#classa_accum_thresh) accordingly.

    - Determine whether the interrupt associated with that class needs a timeout.
      If yes, set [`CLASSA_TIMEOUT_CYC_SHADOWED`](../data/alert_handler.hjson#classa_timeout_cyc_shadowed) to an appropriate value greater than zero (zero corresponds to an infinite timeout and disables the mechanism).

    - For each escalation phase (0..3):
        - Determine length of each escalation phase by setting [`CLASSA_PHASE0_CYC`](../data/alert_handler.hjson#classa_phase0_cyc) accordingly

    - For each escalation signal (0..3):
        - Determine whether to enable the escalation signal, and set the [`CLASSA_CTRL_SHADOWED.E0_EN`](../data/alert_handler.hjson#classa_ctrl_shadowed) bit accordingly (default is enabled).
          Note that setting all of the `E*_EN` bits to 0 within a class has the same effect of disabling the entire class by setting [`CLASSA_CTRL_SHADOWED.EN`](../data/alert_handler.hjson#classa_ctrl_shadowed) to zero.
        - Determine the phase -> escalation mapping of this class and program it via the [`CLASSA_CTRL_SHADOWED.E0_MAP`](../data/alert_handler.hjson#classa_ctrl_shadowed) values if it needs to be changed from the default mapping (0->0, 1->1, 2->2, 3->3).

    - Optionally lock the class configuration by writing 0 to [`CLASSA_CTRL_SHADOWED.REGWEN`](../data/alert_handler.hjson#classa_ctrl_shadowed).

4. After initial configuration at startup, enable the ping timer mechanism by writing 1 to [`PING_TIMER_EN`](../data/alert_handler.hjson#ping_timer_en).
It is also recommended to lock the ping timer configuration by clearing [`PING_TIMER_REGWEN`](../data/alert_handler.hjson#ping_timer_regwen).
Note that only **locked and enabled** alerts are going to be pinged using the ping mechanism.
This ensures that spurious ping failures cannot occur when previously enabled alerts are being disabled again (before locking).

## Interrupt Handling

For every alert that is enabled, an interrupt will be triggered on class A, B, C, or D.
To handle an interrupt of a particular class, software should execute the following steps:

1. If needed, check the escalation state of this class by reading [`CLASSA_STATE`](../data/alert_handler.hjson#classa_state).
   This reveals whether escalation protocol has been triggered and in which escalation phase the class is.
   In case interrupt timeouts are  enabled the class will be in timeout state unless escalation has already been triggered.
   The current interrupt or escalation cycle counter can be read via [`CLASSA_ESC_CNT`](../data/alert_handler.hjson#classa_esc_cnt).

2. Since the interrupt does not indicate which alert triggered, SW must read the cause registers [`LOC_ALERT_CAUSE`](../data/alert_handler.hjson#loc_alert_cause) and [`ALERT_CAUSE`](../data/alert_handler.hjson#alert_cause) etc.
   The cause bits of all alerts are concatenated and chunked into 32bit words.
   Hence the register file contains as many cause words as needed to cover all alerts present in the system.
   Each cause register contains a sticky bit that is set by the incoming alert, and is clearable with a write by software.
   This should only be cleared after software has cleared the event trigger, if applicable.
   It is possible that the event requires no clearing (e.g. a parity error), or can't be cleared (a breach in the metal mesh protecting the chip).

   Note that in the rare case when multiple events are triggered at or about the same time, all events should be cleared before proceeding.

3. After the event is cleared (if needed or possible), software should handle the interrupt as follows:

    - Resetting the accumulation register for the class by writing [`CLASSA_CLR`](../data/alert_handler.hjson#classa_clr).
      This also aborts the escalation protocol if it has been triggered.
      If for some reason it is desired to never allow the accumulator or escalation to be cleared, software can initialize the [`CLASSA_CLR_REGWEN`](../data/alert_handler.hjson#classa_clr_regwen) register to zero.
      If [`CLASSA_CLR_REGWEN`](../data/alert_handler.hjson#classa_clr_regwen) is already false when an alert interrupt is detected (either due to software control or hardware trigger via [`CLASSA_CTRL_SHADOWED.LOCK`](../data/alert_handler.hjson#classa_ctrl_shadowed)), then the accumulation counter can not be cleared and this step has no effect.

    - After the accumulation counter is reset (if applicable), software should clear the class A interrupt state bit [`INTR_STATE.CLASSA`](../data/alert_handler.hjson#intr_state).
      Clearing the class A interrupt state bit also clears and stops the interrupt timeout counter (if enabled).

Note that testing interrupts by writing to the interrupt test registers does also trigger the internal interrupt timeout (if enabled), since the interrupt state is used as enable signal for the timer.
However, alert accumulation will not be triggered by this testing mechanism.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../../sw/device/lib/dif/dif_alert_handler.h)

## Register Table

* [Register Table](../data/alert_handler.hjson#registers)


# Additional Notes

## Timing Constraints

The skew within all differential signal pairs must be constrained to be smaller than the period of the fastest clock operating the alert handler receivers.
The maximum propagation delay of differential pair should also be constrained (although it may be longer than the clock periods involved).


## Fast-track Alerts

Note that it is possible to program a certain class to provide a fast-track response for critical alerts by setting its accumulation trigger value to 1, and configuring the escalation protocol such that the appropriate escalation measure is triggered within escalation phase 0.
This results in a minimal escalation latency of 4 clock cycles from alert sender input to escalation receiver output in the case where all involved signaling modules are completely synchronous with the alert handler.
In case the alert sender is asynchronous w.r.t. to the alert handler, the actual latency depends on the clock periods involved.
Assuming both clocks have the same frequency alert propagation takes at least 6-8 clock alert handler clock cycles.

For alerts that mandate an asynchronous response (i.e. without requiring a clock to be active), it is highly recommended to build a separate network at the top-level.
That network should OR' the critical sources together and route the asynchronous alert signal directly to the highest severity countermeasure device.
Examples for alert conditions of this sort would be attacks on the secure clock.
