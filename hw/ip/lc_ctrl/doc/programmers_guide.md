# Programmer's Guide

The register layout and offsets shown in the [register table](registers.md) below are identical for both the CSR and JTAG TAP interfaces.
Hence the following programming sequences apply to both SW running on the device and SW running on the test appliance that accesses life cycle through the TAP.

## Regular Life Cycle Transitions

1. In order to perform a life cycle transition, SW should first check whether the life cycle controller has successfully initialized and is ready to accept a transition command by making sure that the [`STATUS.READY`](registers.md#status) bit is set to 1, and that all other status and error bits in [`STATUS`](registers.md#status) are set to 0.

2. Read the [`LC_STATE`](registers.md#lc_state) and [`LC_TRANSITION_CNT`](registers.md#lc_transition_cnt) registers to determine which life cycle state the device currently is in, and how many transition attempts are still available.

3. Claim exclusive access to the transition interface by writing `kMuBi8True` to the [`CLAIM_TRANSITION_IF`](registers.md#claim_transition_if) register, and reading it back. If the value read back equals to `kMuBi8True`, the hardware mutex has successfully been claimed and SW can proceed to step 4. If the value read back equals to 0, the mutex has already been claimed by the other interface (either CSR or TAP), and SW should try claiming the mutex again.
Note that all transition interface registers are protected by the hardware-governed [`TRANSITION_REGWEN`](registers.md#transition_regwen) register, which will only be set to 1 if the mutex has been claimed successfully.

4. If required, software can switch to the external clock via the [`TRANSITION_CTRL.EXT_CLK_EN`](registers.md#transition_ctrl--ext_clock_en) register in `RAW`, `TEST*` and `RMA` life cycle states.
   This setting is ignored in the `PROD*` and `DEV` states.

5. Write the desired target state to [`TRANSITION_TARGET`](registers.md#transition_target). For conditional transitions, the corresponding token has to be written to [`TRANSITION_TOKEN`](registers.md#transition_token). For all unconditional transitions, the token registers have to be set to zero.

6. An optional, but recommended step is to read back and verify the values written in steps 4. and 5. before proceeding with step 7.

7. Write 1 to the [`TRANSITION_CMD.START`](registers.md#transition_cmd) register to initiate the life cycle transition.

8. Poll the [`STATUS`](registers.md#status) register and wait until either [`STATUS.TRANSITION_SUCCESSFUL`](registers.md#status) or any of the error bits is asserted.
The [`TRANSITION_REGWEN`](registers.md#transition_regwen) register will be set to 0 while a transition is in progress in order to prevent any accidental modifications of the transition interface registers during this phase.

9. Reset the device so that the new life cycle state becomes effective.

Note that all life cycle state transition increments the `LC_TRANSITION_CNT` and moves the life cycle state into the temporary POST_TRANSITION state - even if the transition was unsuccessful.
Hence, step 8. cannot be carried out in case device SW is used to implement the programming sequence above, since the processor is disabled in the POST_TRANSITION life cycle state.

This behavior is however not of concern, since access to the transition interface via the CSRs is considered a convenience feature for bringup in the lab.
It is expected that the JTAG TAP interface is used to access the life cycle transition interface in production settings.

## Volatile `RAW` -> `TEST_UNLOCKED0` Transition

Note that this functionality is only available on test chips where the design is compiled with SecVolatileRawUnlockEn = 1.
On production silicon this option will be disabled.

1. In order to perform a volatile `RAW` -> `TEST_UNLOCKED0` life cycle transition, SW should first check whether the life cycle controller has successfully initialized and is ready to accept a transition command by making sure that the [`STATUS.READY`](registers.md#status) bit is set to 1, and that all other status and error bits in [`STATUS`](registers.md#status) are set to 0.

2. Read the [`LC_STATE`](registers.md#lc_state) and [`LC_TRANSITION_CNT`](registers.md#lc_transition_cnt) registers and make sure that the device is in the `RAW` life cycle state.

3. Claim exclusive access to the transition interface by writing `kMuBi8True` to the [`CLAIM_TRANSITION_IF`](registers.md#claim_transition_if) register, and reading it back.
   If the value read back equals to `kMuBi8True`, the hardware mutex has successfully been claimed and SW can proceed to step 4. If the value read back equals to 0, the mutex has already been claimed by the other interface (either CSR or TAP), and SW should try claiming the mutex again.
   Note that all transition interface registers are protected by the hardware-governed [`TRANSITION_REGWEN`](registers.md#transition_regwen) register, which will only be set to 1 if the mutex has been claimed successfully.

4. To request a volatile `RAW` -> `TEST_UNLOCKED0` transition SW should set the [`TRANSITION_CTRL.VOLATILE_RAW_UNLOCK`](#transition_ctrl--volatile_raw_unlock) to 1.
   Software can check whether volatile unlock is supported by reading the register after writing 1 to it.
   If the mechanism is available, the register reads back as 1, otherwise it reads back 0.

5. If required, software can switch to the external clock via the [`TRANSITION_CTRL.EXT_CLK_EN`](registers.md#transition_ctrl--ext_clock_en) register.

6. Write `TEST_UNLOCKED0` to [`TRANSITION_TARGET`](registers.md#transition_target).
   The [`TRANSITION_TOKEN`](registers.md#transition_token) needs to be set to the **hashed** unlock token value, since the value written will not be passed through KMAC in this case.

7. An optional, but recommended step is to read back and verify the values written in steps 4. - 6. before proceeding with step 8.

8. If the goal is to gain access to either of the TAPs that are only available in `TEST_UNLOCKED*` life cycle states, the hardware straps should be applied before proceeding to the next step.
   The pinmux will resample them if the volatile unlock operation is successful and steer the TAP selection demux accordingly.

9. Write 1 to the [`TRANSITION_CMD.START`](registers.md#transition_cmd) register to initiate the life cycle transition.

10. Poll the [`STATUS`](registers.md#status) register and wait until either [`STATUS.TRANSITION_SUCCESSFUL`](registers.md#status) or any of the error bits is asserted.
   The [`TRANSITION_REGWEN`](registers.md#transition_regwen) register will be set to 0 while a transition is in progress in order to prevent any accidental modifications of the transition interface registers during this phase.

Note that if a volatile `RAW` unlock operation has been performed, it is not necessary to reset the chip and the life cycle controller accepts further transition commands.
The `LC_TRANSITION_CNT`  will not be incremented and the life cycle state will not be moved to the temporary POST_TRANSITION state.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_lc_ctrl.h)
