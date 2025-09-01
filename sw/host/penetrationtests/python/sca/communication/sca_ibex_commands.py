# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Communication interface for the Ibex SCA application on OpenTitan.

Communication with OpenTitan happens over the uJson command interface.
"""
import json
import time
from sw.host.penetrationtests.python.util import common_library


class OTIbex:
    def __init__(self, target) -> None:
        self.target = target

    def _ujson_ibex_sca_cmd(self):
        self.target.write(json.dumps("IbexSca").encode("ascii"))
        time.sleep(0.003)

    def init(
        self,
        core_config: dict = common_library.default_core_config,
        sensor_config: dict = common_library.default_sensor_config,
    ) -> tuple:
        """Initializes the Ibex SCA tests on the target.

        Returns:
           Device id
           The owner info page
           The boot log
           The boot measurements
           The testOS version
        """

        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # Init command.
        self.target.write(json.dumps("Init").encode("ascii"))

        # Write each configuration block to the target.
        self.target.write(json.dumps(core_config).encode("ascii"))
        self.target.write(json.dumps(sensor_config).encode("ascii"))

        device_id = self.target.read_response()
        owner_page = self.target.read_response()
        boot_log = self.target.read_response()
        boot_measurements = self.target.read_response()
        version = self.target.read_response()
        return device_id, owner_page, boot_log, boot_measurements, version

    def ibex_sca_register_file_read_batch_random(self, num_segments: int):
        """Start ibex.sca.register_file_read_batch_random test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFReadBatchRandom command.
        self.target.write(json.dumps("RFReadBatchRandom").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_register_file_read(self, data: list[int]):
        """Start ibex.sca.register_file_read test.
        Args:
            data: The data that is first written into the RF and then read back.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFRead command.
        self.target.write(json.dumps("RFRead").encode("ascii"))
        # Data payload.
        data = {"data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_register_file_read_batch_fvsr(self, data: int, num_segments: int):
        """Start ibex.sca.register_file_read_batch_fvsr test.
        Args:
            data: The data that is first written into the RF and then read back.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFReadBatchFvsr command.
        self.target.write(json.dumps("RFReadBatchFvsr").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_register_file_write_batch_random(self, num_segments: int):
        """Start ibex.sca.register_file_write_batch_random test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFWriteBatchRandom command.
        self.target.write(json.dumps("RFWriteBatchRandom").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_register_file_write(self, data: list[int]):
        """Start ibex.sca.register_file_write test.
        Args:
            data: The data that is written into the RF.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFWrite command.
        self.target.write(json.dumps("RFWrite").encode("ascii"))
        # Data payload.
        data = {"data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_register_file_write_batch_fvsr(self, data: int, num_segments: int):
        """Start ibex.sca.register_file_write_batch_fvsr test.
        Args:
            data: The data that is written into the RF.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # RFWriteBatchFvsr command.
        self.target.write(json.dumps("RFWriteBatchFvsr").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_write_batch_random(self, num_segments: int):
        """Start ibex.sca.tl_write_batch_random test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLWriteBatchRandom command.
        self.target.write(json.dumps("TLWriteBatchRandom").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_write_batch_random_fix_address(self, num_segments: int):
        """Start ibex.sca.tl_write_batch_random_fix_address test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLWriteBatchRandomFixAddress command.
        self.target.write(json.dumps("TLWriteBatchRandomFixAddress").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_write(self, data: list[int]):
        """Start ibex.sca.tl_write_random test.
        Args:
            data: The data that is written into the SRAM over Tl-UL.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLWrite command.
        self.target.write(json.dumps("TLWrite").encode("ascii"))
        # Data payload.
        data = {"data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_write_batch_fvsr(self, data: int, num_segments: int):
        """Start ibex.sca.tl_write_batch_fvsr test.
        Args:
            data: The data that is written into the SRAM over Tl-UL.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLWriteBatchFvsr command.
        self.target.write(json.dumps("TLWriteBatchFvsr").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_write_batch_fvsr_fix_address(self, data: int, num_segments: int):
        """Start ibex.sca.tl_write_batch_fvsr_fix_address test.
        Args:
            data: The data that is written into the SRAM over Tl-UL.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLWriteBatchFvsrFixAddress command.
        self.target.write(json.dumps("TLWriteBatchFvsrFixAddress").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_read_batch_random(self, num_segments: int):
        """Start ibex.sca.tl_read_batch_random test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLReadBatchRandom command.
        self.target.write(json.dumps("TLReadBatchRandom").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_read_batch_random_fix_address(self, num_segments: int):
        """Start ibex.sca.tl_read_batch_random_fix_address test.
        Args:
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLReadBatchRandomFixAddress command.
        self.target.write(json.dumps("TLReadBatchRandomFixAddress").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_read(self, data: list[int]):
        """Start ibex.sca.tl_read test.
        Args:
            num_iterations: The number of iterations the RF is written.
            data: The data that is written into the SRAM over Tl-UL.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLRead command.
        self.target.write(json.dumps("TLRead").encode("ascii"))
        # Data payload.
        data = {"data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_read_batch_fvsr(self, data: int, num_segments: int):
        """Start ibex.sca.tl_read_batch_fvsr test.
        Args:
            data: The data that is written into the SRAM over Tl-UL.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLReadBatchFvsr command.
        self.target.write(json.dumps("TLReadBatchFvsr").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_tl_read_batch_fvsr_fix_address(self, data: int, num_segments: int):
        """Start ibex.sca.tl_read_batch_fvsr_fix_address test.
        Args:
            data: The data that is written into the SRAM over Tl-UL.
            num_segments: The number of iterations.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # TLReadBatchFvsrFixAddress command.
        self.target.write(json.dumps("TLReadBatchFvsrFixAddress").encode("ascii"))
        # Data payload.
        data = {"num_iterations": num_segments, "fixed_data": data}
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_combi_operations_batch_fvsr(
        self, num_iterations: int, trigger: int, fixed_data1: int, fixed_data2: int
    ):
        """Start ibex.sca.combi_operations_batch_fvsr test.
        Args:
            num_iterations: The number of iterations the test is repeated.
            trigger: 12-bit value, each bit sets the trigger for one of the 12 trigger windows.
            fixed_data1: The first fixed value.
            fixed_data2: The second fixed value.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # CombiOperationsBatchFvsr command.
        self.target.write(json.dumps("CombiOperationsBatchFvsr").encode("ascii"))
        # Input payload.
        data = {
            "num_iterations": num_iterations,
            "trigger": trigger,
            "fixed_data1": fixed_data1,
            "fixed_data2": fixed_data2,
        }
        self.target.write(json.dumps(data).encode("ascii"))

    def ibex_sca_combi_operations_batch(
        self, num_iterations: int, trigger: int, fixed_data1: int, fixed_data2: int
    ):
        """Start ibex.sca.combi_operations_batch test.
        Args:
            num_iterations: The number of iterations the test is repeated.
            trigger: 12-bit value, each bit sets the trigger for one of the 12 trigger windows.
            fixed_data1: The first fixed value.
            fixed_data2: The second fixed value.
        """
        # IbexSca command.
        self._ujson_ibex_sca_cmd()
        # CombiOperationsBatchFvsr command.
        self.target.write(json.dumps("CombiOperationsBatch").encode("ascii"))
        # Input payload.
        data = {
            "num_iterations": num_iterations,
            "trigger": trigger,
            "fixed_data1": fixed_data1,
            "fixed_data2": fixed_data2,
        }
        self.target.write(json.dumps(data).encode("ascii"))

    def start_test(self, testname: str, arg1=None, arg2=None, arg3=None, arg4=None) -> None:
        """Start the selected test.

        Call the function selected in the config file. Uses the getattr()
        construct to call the function.

        Args:
            testname: The test to start
            arg1: The first argument passed to the test.
            arg2: The second argument passed to the test.
        """
        test_function = getattr(self, testname)
        if arg1 is not None and arg2 is None and arg3 is None and arg4 is None:
            test_function(arg1)
        elif arg2 is not None and arg3 is None and arg4 is None:
            test_function(arg1, arg2)
        elif arg3 is not None and arg4 is None:
            test_function(arg1, arg2, arg3)
        elif arg4 is not None:
            test_function(arg1, arg2, arg3, arg4)
        else:
            test_function()
