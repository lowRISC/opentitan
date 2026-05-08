# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from .csr import CSRFile
from .ispr import DumbISPR
from .mai_ispr import MaiOperation
from .wsr import WSRFile

# The masking accelerator interface (MAI) emulates the behavior of the interface and the actual
# accelerators.

# Enable or disable assertions which check that the inputs and outputs of the accelerators
# meet certain constraints (e.g., being smaller than the modulus).
CHECK_ACCELERATOR_CONSTRAINTS = False

# Latencies of the accelerators in cycles.
ACCELERATOR_LATENCIES = {
    MaiOperation.A2B: 32,
    MaiOperation.B2A: 32,
    MaiOperation.SECADD: 32,
}


class MaskingAccelerator:
    '''Models a masking accelerator which has a simple pipeline.
    New operations can be pushed to the accelerator, and results can be popped from it.
    Each step of the simulation advances the pipeline by one stage.
    '''

    def __init__(self, latency: int, mod_wsr: DumbISPR) -> None:
        # Latency of the masking accelerator in cycles.
        self.latency = latency

        # The MOD WSR is used to get the current modulus for operations.
        self.mod_wsr = mod_wsr

        # The pipeline contains the two result shares and is modeled with a deque where None
        # indicates an empty slot.
        self.pipeline: List[Optional[Tuple[int, int]]]
        self.pipeline = [None] * self.latency

    def push(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> bool:
        '''Try to push an operation to the masking accelerator pipeline.

        Returns True if the accelerator can accept it (free pipeline slot), False otherwise.
        '''
        # This accelerator implementation features no backpressure, so we always accept new
        # operations. Pop the leftmost pipeline slot and replace it with the new operation result.
        # The result is computed immediately but will only be available after the full pipeline
        # latency.
        self.pipeline[0] = self._compute(in0_s0, in0_s1, in1_s0, in1_s1)
        return True

    def peek(self) -> Optional[Tuple[int, int]]:
        '''Read the current output of the masking accelerator pipeline.'''
        return self.pipeline[-1]

    def step(self) -> None:
        '''Advance the pipeline by one stage if possible.'''
        # This accelerator implementation features no backpressure, so we always advance the
        # pipeline. We insert an unused pipeline slot which is replaced in case a new item is
        # pushed. The last element is dropped.
        none: List[Optional[Tuple[int, int]]] = [None]
        self.pipeline = none + self.pipeline[:self.latency - 2]

    def is_busy(self) -> bool:
        '''Return True if the accelerator is busy (has pending operations), False otherwise.'''
        # The accelerator is busy if there is at least one non-None item in the pipeline.
        return any(slot is not None for slot in self.pipeline)

    def _modulus(self) -> int:
        '''Return the bits 31:0 of the MOD WSR, for use as a modulus.'''
        return self.mod_wsr.read_unsigned() & ((1 << 32) - 1)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        '''Compute the result of the masking operation.'''
        raise NotImplementedError


class A2BAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbISPR):
        super().__init__(ACCELERATOR_LATENCIES[MaiOperation.A2B], mod_wsr)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        # The current placeholder implementation removes the arithmetic mask and adds a new boolean
        # mask. We use a fixed mask until the exact design is known.
        #
        # Input: (x - s mod q, s), (x - s) + s mod q = x,  0 <= s < q
        # Output: (x XOR r, r), (x XOR r) XOR r = x, 0 <= x, r < 2^k

        # in1_s0 and in1_s1 are not used by the A2B accelerator

        s = in0_s1
        # We take a fixed mask which satisfies the constraints until the exact design is known.
        r = self._modulus() // 3
        secret = (in0_s0 + s) % self._modulus()
        masked_secret = (secret ^ r)

        # Optionally, we crash if the constraints are not met.
        if CHECK_ACCELERATOR_CONSTRAINTS:
            assert self._modulus() < 2**32
            assert 0 <= s < self._modulus()
            assert 0 <= r < 2**32
            assert 0 <= secret < self._modulus()

        # Limit results to 32 bits
        masked_secret &= ((1 << 32) - 1)
        r &= ((1 << 32) - 1)
        return (masked_secret, r)


class B2AAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbISPR):
        super().__init__(ACCELERATOR_LATENCIES[MaiOperation.B2A], mod_wsr)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        # The current placeholder implementation removes the boolean mask and adds a new arithmetic
        # mask. We use a fixed mask until the exact design is known.
        #
        # Input: (x XOR r, r), 0 <= x, r < 2^k
        # Output: (x - s mod q, s), (x - s) + s mod q = x, 0 <= s < q

        # in1_s0 and in1_s1 are not used by the B2A accelerator

        # We take a fixed mask which satisfies the constraints until the exact design is known.
        s = self._modulus() // 3
        r = in0_s1

        secret = in0_s0 ^ r
        masked_secret = (secret - s) % self._modulus()

        # Optionally, we crash if the constraints are not met.
        if CHECK_ACCELERATOR_CONSTRAINTS:
            assert self._modulus() < 2**32
            assert 0 <= in0_s0 < self._modulus()
            assert 0 <= r < 2**32
            assert 0 <= s < self._modulus()

        # Limit results to 32 bits
        masked_secret &= ((1 << 32) - 1)
        s &= ((1 << 32) - 1)
        return (masked_secret, s)


class SecAddModkAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbISPR):
        super().__init__(ACCELERATOR_LATENCIES[MaiOperation.SECADD], mod_wsr)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        # The current placeholder implementation removes the boolean masks, adds the secrets
        # modulo 2**32, and adds a new boolean mask. We use a fixed mask until the exact design is
        # known.
        #
        # Input: (x xor r1, r1), (y xor s1, s1), 0 <= x, y, s, r < q < 2^k
        # Output: ((x + y mod q) XOR t, t)
        r1 = in0_s1
        s1 = in1_s1
        # We take a fixed mask until the exact design is known.
        t = self._modulus() // 3

        x = in0_s0 ^ r1
        y = in1_s0 ^ s1
        sum = (x + y) % 2**32
        masked_sum = sum ^ t

        if CHECK_ACCELERATOR_CONSTRAINTS:
            assert self._modulus() < 2**32
            assert 0 <= x < self._modulus()
            assert 0 <= y < self._modulus()
            assert 0 <= r1 < self._modulus()
            assert 0 <= s1 < self._modulus()

        # Limit results to 32 bits
        masked_sum &= ((1 << 32) - 1)
        t &= ((1 << 32) - 1)
        return (masked_sum, t)


class MaskingAcceleratorInterface:
    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.on_start(csrs, wsrs)

    def _accelerator(self) -> MaskingAccelerator:
        '''Return the currently selected masking accelerator based on the operation field.'''
        return self._all_accelerators[self.csrs.MAI_CTRL.current_operation()]

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        '''Reset the MAI for the start of an OTBN execution'''
        self.csrs = csrs
        self.wsrs = wsrs

        # All available accelerators are instantiated here in a dictionary.
        # The currently active accelerator is selected based on the operation field in MAI_CTRL.
        # Changing the operation while an operation is ongoing is not allowed (see
        # is_valid_ctrl_change). Thus, the step() method can simply read the operation field each
        # cycle to get the current accelerator.
        # TODO: Decide whether the accelerators are reset or not
        self._all_accelerators = {
            MaiOperation.A2B: A2BAccelerator(self.wsrs.MOD),
            MaiOperation.B2A: B2AAccelerator(self.wsrs.MOD),
            MaiOperation.SECADD: SecAddModkAccelerator(self.wsrs.MOD),
        }

        # Dispatch related variables
        # The dispatch logic is responsible for pushing inputs into the accelerator.
        self._dispatch_idx = 0
        self.is_dispatching = False

        # Writeback related variables
        # The writeback logic is responsible for receiving results from the accelerator into the
        # output WSRs.
        self._writeback_idx = 0

    def step(self) -> None:
        '''Advance the MAI simulation by one cycle.

        This is expected to be called before the current instruction executes / steps.'''
        # The step logic sets bits and values in the cycle where the instruction can read it which
        # is different compared to how CRSs are updated when an instruction writes to them.
        # Setting values "immediately" simplifies the status flag handling because the abort case
        # must not be considered.

        # Writeback logic:
        # Get the newest result and write it into the output WSRs. This is done before
        # advancing the pipeline to model the fact that the result is available at
        # the start of the cycle.
        results = self._accelerator().peek()
        if results is not None:
            # Write to the output WSRs
            self.wsrs.MAI_RES_S0.set_32bit_unsigned(results[0], self._writeback_idx)
            self.wsrs.MAI_RES_S1.set_32bit_unsigned(results[1], self._writeback_idx)
            self._writeback_idx += 1

        # Detect if we finished writing back
        if self._writeback_idx >= 8:
            self._writeback_idx = 0
            # Reset the busy bit in the cycle where the last result is set.
            self.csrs.MAI_STATUS.update_busy_bit(False)

        # Advance the accelerator pipeline
        self._accelerator().step()

        # Start a new operation if start bit was set in last cycle
        if self.csrs.MAI_CTRL.is_start_bit_set():
            # The start bit may only be set if the MAI is not busy. If this assertion fails, the
            # check when writing to the MAI_CTRL CSR is wrong.
            assert not self.csrs.MAI_STATUS.is_busy()
            # Begin pushing inputs in the dispatch logic
            self.is_dispatching = True
            # Immediately set the busy bit so the current instruction is not allowed to start the
            # next execution.
            self.csrs.MAI_STATUS.update_busy_bit(True)
            # Immediately reset the ready bit such that any configuration change check does not
            # allow changing the operation type.
            self.csrs.MAI_STATUS.update_ready_bit(False)
            # Immediately reset the start bit such that it always reads zero.
            self.csrs.MAI_CTRL.update_start_bit(False)

        if self.is_dispatching:
            self._accelerator().push(self.wsrs.MAI_IN0_S0.read_32bit_unsigned(self._dispatch_idx),
                                     self.wsrs.MAI_IN0_S1.read_32bit_unsigned(self._dispatch_idx),
                                     self.wsrs.MAI_IN1_S0.read_32bit_unsigned(self._dispatch_idx),
                                     self.wsrs.MAI_IN1_S1.read_32bit_unsigned(self._dispatch_idx))
            self._dispatch_idx += 1

        # Detect if we have finished dispatching
        if self._dispatch_idx >= 8:
            self._dispatch_idx = 0
            self.is_dispatching = False
            # Immediately set the ready bit as the input WSRs can be overwritten in this cycle.
            self.csrs.MAI_STATUS.update_ready_bit(True)

    def is_busy(self) -> bool:
        '''Returns whether the MAI is currently busy processing an operation.'''
        return self.csrs.MAI_STATUS.is_busy()

    def is_ready(self) -> bool:
        '''Returns whether the MAI is ready to accept new inputs.'''
        return self.csrs.MAI_STATUS.is_ready()

    def ready_for_inputs(self) -> bool:
        return self.is_ready()

    def ready_to_start(self) -> bool:
        return not self.is_busy()

    def is_valid_ctrl_change(self, value: int) -> bool:
        '''Return whether writing value to the MAI_CTRL CSR is currently allowed.'''
        # Starting is only allowed if MAI is ready.
        if self.csrs.MAI_CTRL.would_set_start_bit(value) and not self.ready_to_start():
            return False

        # We only allow setting the operation to valid options.
        if not self.csrs.MAI_CTRL.is_valid_operation(value):
            return False

        # Changing the operation is only allowed if MAI is not busy / no operation is ongoing.
        if self.csrs.MAI_CTRL.would_change_op(value) and self.is_busy():
            return False

        return True
