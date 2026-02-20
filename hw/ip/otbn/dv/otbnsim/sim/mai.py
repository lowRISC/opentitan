# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional, Tuple
from collections import deque

from .csr import CSRFile, MaiOperation
from .wsr import WSRFile, DumbWSR

# The masking accelerator interface (MAI) emulates the behavior of the interface and the actual
# accelerators.

# Enable or disable assertions which check that the inputs and outputs of the accelerators
# meet certain constraints (e.g., being smaller than the modulus).
CHECK_ACCELERATOR_CONSTRAINTS = False


class MaskingAccelerator:
    '''Models a masking accelerator which has a simple pipeline.
    New operations can be pushed to the accelerator, and results can be popped from it.
    Each step of the simulation advances the pipeline by one stage.
    '''

    def __init__(self, latency: int, mod_wsr: DumbWSR) -> None:
        # Latency of the masking accelerator in cycles.
        self.latency = latency

        # The MOD WSR is used to get the current modulus for operations.
        self.mod_wsr = mod_wsr

        # The pipeline contains the two result shares and is modeled with a deque where None
        # indicates an empty slot.
        self.pipeline: deque[Optional[Tuple[int, int]]]
        self.pipeline = deque([None] * self.latency, self.latency)

    def push(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> bool:
        '''Try to push an operation to the masking accelerator pipeline.

        Returns True if the accelerator can accept it (free pipeline slot), False otherwise.
        '''
        # This accelerator implementation features no backpressure, so we always accept new
        # operations. Pop the leftmost pipeline slot and replace it with the new operation result.
        # The result is computed immediately but will only be available after the full pipeline
        # latency.
        self.pipeline.popleft()
        self.pipeline.appendleft(self._compute(in0_s0, in0_s1, in1_s0, in1_s1))
        return True

    def pop(self) -> Optional[Tuple[int, int]]:
        '''Read the current output of the masking accelerator pipeline.'''
        # We do only peak the pipeline as the pipeline advancing is modelled in the step() method.
        return self.pipeline[-1]

    def step(self) -> None:
        '''Advance the pipeline by one stage if possible.'''
        # This accelerator implementation features no backpressure, so we always advance the
        # pipeline. We insert an unused pipeline slot which is replaced in case a new item is
        # pushed. appendleft() will drop the rightmost item automatically.
        self.pipeline.appendleft(None)

    def is_busy(self) -> bool:
        '''Return True if the accelerator is busy (has pending operations), False otherwise.'''
        # The accelerator is busy if there is at least one non-None item in the pipeline.
        return any(slot is not None for slot in self.pipeline)

    def _modulus(self) -> int:
        '''Return the current 32-bit modulus from the modulus WSR.'''
        return self.mod_wsr.read_unsigned() & ((1 << 32) - 1)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        '''Compute the result of the masking operation.'''
        raise NotImplementedError


class A2BAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbWSR):
        super().__init__(32, mod_wsr)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        # The current placeholder implementation removes the arithmetic mask and adds a new boolean
        # mask. We use a fixed mask until the exact design is known.
        #
        # Input: (x - s mod q, s),  (x - s) + s mod q = x,  0 <= s < q
        # Output: (x XOR r, r),  x XOR r XOR r = x, 0 <= x, r < q <  2^k

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
            assert 0 <= r < self._modulus()
            assert 0 <= secret < self._modulus()

        # Limit results to 32 bits
        masked_secret &= ((1 << 32) - 1)
        r &= ((1 << 32) - 1)
        return (masked_secret, r)


class B2AAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbWSR):
        super().__init__(32, mod_wsr)

    def _compute(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int) -> Tuple[int, int]:
        # The current placeholder implementation removes the boolean mask and adds a new arithmetic
        # mask. We use a fixed mask until the exact design is known.
        #
        # Input: (x XOR r, r), 0 <= x, r < q <  2^k
        # Output: (x - s mod q, s),  (x - s) + s mod q = x,  0 <= s < q

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
            assert 0 <= r < self._modulus()
            assert 0 <= s < self._modulus()

        # Limit results to 32 bits
        masked_secret &= ((1 << 32) - 1)
        s &= ((1 << 32) - 1)
        return (masked_secret, s)


class SecAddModkAccelerator(MaskingAccelerator):
    def __init__(self, mod_wsr: DumbWSR):
        super().__init__(32, mod_wsr)

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

        # The CSRs and WSRs
        self.csrs = csrs
        self.wsrs = wsrs
        self.mai_ctrl = self.csrs.MaiCtrl
        self.mai_status = self.csrs.MaiStatus
        self.mai_res_s0 = self.wsrs.MaiResS0
        self.mai_res_s1 = self.wsrs.MaiResS1
        self.mai_in0_s0 = self.wsrs.MaiIn0S0
        self.mai_in0_s1 = self.wsrs.MaiIn0S1
        self.mai_in1_s0 = self.wsrs.MaiIn1S0
        self.mai_in1_s1 = self.wsrs.MaiIn1S1

        # All available accelerators are instantiated here in a dictionary.
        # The currently active accelerator is selected based on the operation field in MAI_CTRL.
        # Changing the operation while an operation is ongoing is not allowed (see
        # is_valid_ctrl_change). Thus, the step() method can simply read the operation field each
        # cycle to get the current accelerator like this:
        # self._all_accelerators[self.mai_ctrl.read_operation()]
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

    def _accelerator(self) -> MaskingAccelerator:
        '''Return the currently selected masking accelerator based on the operation field.'''
        return self._all_accelerators[self.mai_ctrl.read_operation()]

    def step(self) -> None:
        '''Advance the MAI simulation by one cycle.

        This is expected to be called before the current instruction executes / steps.
        '''
        ###################
        # Writeback logic #
        ###################
        # Get the newest result and write it into the output WSRs. This is done before
        # advancing the pipeline to model the fact that the result is available at
        # the start of the cycle.
        results = self._accelerator().pop()
        if results is not None:
            # Write to the output WSRs
            self.mai_res_s0.set_32bit_unsigned(results[0], self._writeback_idx)
            self.mai_res_s1.set_32bit_unsigned(results[1], self._writeback_idx)
            self._writeback_idx += 1

        # Detect if we finished writing back
        if self._writeback_idx >= 8:
            self._writeback_idx = 0
            # If we are finishing the writeback, reset the busy bit. The write method update the
            # bits when committing to the changes so the current instruction still reads the old
            # value.
            self.mai_status.write_busy_bit(False)

        ######################
        # Accelerator update #
        ######################
        # Advance the accelerator pipeline.
        self._accelerator().step()

        #################
        # Start logic   #
        #################
        # Start a new operation if start bit was set in last cycle
        if self.mai_ctrl.read_start_bit():
            # Begin pushing inputs in the dispatch logic
            self.is_dispatching = True
            # Immediately set the busy bit such that the current instruction reads it as set.
            self.mai_status.set_busy_bit(True)
            # Immediately reset the ready bit such that the current instruction reads it as reset
            # and any configuration change check does not allow changing the operation type.
            self.mai_status.set_ready_bit(False)
            # Immediately reset the start bit such that it always reads zero.
            self.mai_ctrl.set_start_bit(False)

        ##################
        # Dispatch logic #
        ##################
        if self.is_dispatching:
            self._accelerator().push(self.mai_in0_s0.read_32bit_unsigned(self._dispatch_idx),
                                     self.mai_in0_s1.read_32bit_unsigned(self._dispatch_idx),
                                     self.mai_in1_s0.read_32bit_unsigned(self._dispatch_idx),
                                     self.mai_in1_s1.read_32bit_unsigned(self._dispatch_idx))
            self._dispatch_idx += 1

        # Detect if we have finished dispatching
        if self._dispatch_idx >= 8:
            self._dispatch_idx = 0
            self.is_dispatching = False
            # Set the ready bit at the end of this cycle. This indicates that new inputs can be
            # accepted.
            self.mai_status.write_ready_bit(True)

    def is_busy(self) -> bool:
        '''Returns whether the MAI is currently busy processing an operation.'''
        return self.mai_status.read_busy_bit()

    def is_ready(self) -> bool:
        '''Returns whether the MAI is ready to accept new inputs.'''
        return self.mai_status.read_ready_bit()

    def ready_for_inputs(self) -> bool:
        return self.is_ready()

    def ready_to_start(self) -> bool:
        return not self.is_busy()

    def is_valid_ctrl_change(self, value: int) -> bool:
        '''Return whether writing value to the MAI_CTRL CSR is currently allowed.'''
        # Starting is only allowed if MAI is ready.
        if self.mai_ctrl.would_set_start_bit(value) and not self.ready_to_start():
            return False

        # We only allow setting the operation to valid options.
        if not self.mai_ctrl.is_valid_operation(value):
            return False

        # Changing the operation is only allowed if MAI is not busy / no operation is ongoing.
        if self.mai_ctrl.would_change_op(value) and self.is_busy():
            return False

        return True
