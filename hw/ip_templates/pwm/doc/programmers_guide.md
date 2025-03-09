# Programmer's Guide

To set the PWM Frequency for the entire IP:
1. Clear [`CFG.CNTR_EN`](registers.md#cfg)
2. Select [`CFG.CLK_DIV`](registers.md#cfg)
3. Assert [`CFG.CNTR_EN`](registers.md#cfg)

To configure the fixed PWM duty cycle and for a particular output channel (for example channel 0):

1. Disable blinking by clearing the [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) bit.
2. Set [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle)
3. Optionally set [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param) to adjust the pulse phase.
4. Optionally assert [`INVERT.INVERT_0`](registers.md#invert) to flip the polarity.
5. Set [`PWM_EN.EN_0`](registers.md#pwm_en) to turn the channel on.

These changes will take place immediately, regardless of whether the `phase_ctr` is currently in the middle of a pulse cycle.

To activate simple blinking for channel 0:

1. Set [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) and [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) to establish the initial and target duty cycles.
2. Clear the [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) and [`PWM_PARAM_0.HTBT_EN_0`](registers.md#pwm_param) bits.
This step is necessary for changing the blink timing parameters
3. Set  [`BLINK_PARAM_0.X_0`](registers.md#blink_param) and [`BLINK_PARAM_0.Y_0`](registers.md#blink_param) to set the number of pulse cycles respectively spent at duty cycle A and duty cycle B.
4. Re-assert [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param).

For synchronous blinking of a group of channels, first disable the desired channels using the [`PWM_EN`](registers.md#pwm_en) register.
Then after configuring the blink properties of the entire group, re-enable them with a single write to [`PWM_EN`](registers.md#pwm_en).

To activate heartbeat blinking for channel 0:
1. Set [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) and [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) to establish the initial and target duty cycles.
2. Clear the [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) bit.
This step is necessary for changing the blink timing parameters
3. Set [`BLINK_PARAM_0.X_0`](registers.md#blink_param) to the number of pulse cycles between duty cycle steps (i.e. increments or decrements).
4. Set [`BLINK_PARAM_0.Y_0`](registers.md#blink_param) to set the size of each step.
5. In a single write, assert both [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) and [`PWM_PARAM_0.HTBT_EN_0`](registers.md#pwm_param)

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_pwm.h)
