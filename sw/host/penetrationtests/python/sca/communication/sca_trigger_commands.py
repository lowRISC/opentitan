# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the SHA3 SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson
command interface.
"""
import json
import time
from typing import Optional


class OTTRIGGER:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_trigger_sca_cmd(self):
        self.target.write(json.dumps("TriggerSca").encode("ascii"))
        time.sleep(0.003)

    def select_trigger(self, trigger_source: Optional[int] = 0):
        """Select the trigger source for SCA.
        Args:
            trigger_source:
                            - 0: Precise, hardware-generated trigger - FPGA only.
                            - 1: Fully software-controlled trigger.
        """
        self._ujson_trigger_sca_cmd()
        # SelectTriggerSource command.
        self.target.write(json.dumps("SelectTriggerSource").encode("ascii"))
        # Source payload.
        src = {"source": trigger_source}
        self.target.write(json.dumps(src).encode("ascii"))

    def sensor_config(self, enable: bool = True, clear: bool = True):
        """Configure and/or clear the on-chip background SCA sensor ring buffer."""
        self._ujson_trigger_sca_cmd()
        self.target.write(json.dumps("SensorConfig").encode("ascii"))
        cfg = {"enable": enable, "clear": clear}
        self.target.write(json.dumps(cfg).encode("ascii"))

    def read_sensor_batch(self) -> dict:
        """Drain all available background SCA sensor samples from the target ring buffer."""
        mcycle_deltas = []
        clock_drift = []
        total_captured = 0
        while True:
            self._ujson_trigger_sca_cmd()
            self.target.write(json.dumps("SensorReadBatch").encode("ascii"))
            batch = None
            for _ in range(15):
                resp_str = self.target.read_response()
                if not resp_str:
                    continue
                cand = json.loads(resp_str)
                if isinstance(cand, dict) and "num_samples" in cand:
                    batch = cand
                    break
            if batch is None:
                raise RuntimeError("Timed out waiting for SensorReadBatch response")
            n = batch["num_samples"]
            if batch["total_triggers"] > total_captured:
                total_captured = batch["total_triggers"]
            if n > 0:
                mcycle_deltas.extend(batch["mcycle_deltas"][:n])
                clock_drift.extend(batch["clock_drift"][:n])
            if n < 64:
                break
        return {
            "num_samples": len(mcycle_deltas),
            "total_captured": total_captured,
            "mcycle_deltas": mcycle_deltas,
            "clock_drift": clock_drift,
        }
